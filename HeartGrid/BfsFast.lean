import Std.Data.HashSet
import HeartGrid.Bfs
/-!
# The same verified search, with a hash set

`Bfs.lean` uses lists, which the kernel can evaluate but only for small state spaces.
This variant keeps the visited states in a `Std.HashSet`, so it scales to hundreds of thousands
of states when evaluated by compiled code (`native_decide`).  The soundness theorem is the same and
is proved for every level; only *running* the check is delegated to the compiler.
-/
namespace HeartGrid
open Std

/-- Equal states hash equally (trivially, since `==` on `State` is propositional equality).
This is what lets us use `Std.HashSet`'s lemmas. -/
instance : LawfulHashable State := ⟨fun a b h => by rw [eq_of_beq h]⟩

/-- The fold body of `expandH`: record `x` as visited, and as new, if it has not been seen. -/
def addNewH (acc : HashSet State × List State) (x : State) : HashSet State × List State :=
  if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)

/-- One BFS layer, with a hash set of visited states instead of a list (same algorithm as
`expand`, but membership tests are O(1) so large searches finish quickly). -/
def expandH (L : Level) (V : HashSet State) (F : List State) : HashSet State × List State :=
  (F.flatMap (succs L)).foldl addNewH (V, [])

/-- The state is not at the door. -/
def notWin (L : Level) (s : State) : Bool := decide (s.player ≠ L.exit)

/-- (visited, frontier, no state seen so far is a win) after `k` layers. -/
def bfsStateH (L : Level) : Nat → HashSet State × List State × Bool
  | 0 => ((∅ : HashSet State).insert L.start, [L.start], notWin L L.start)
  | k + 1 =>
    let p := bfsStateH L k
    let q := expandH L p.1 p.2.1
    (q.1, q.2, p.2.2 && q.2.all (notWin L))

/-- The fast checker: `true` when no state within `k` actions of the start is a win.
Evaluated by compiled code (`native_decide`) for the big rooms. -/
def bfsNoWinH (L : Level) (k : Nat) : Bool := (bfsStateH L k).2.2

/-! ### Proof -/

/-- Hash-set version of `fold_spec`; see there for the meaning of the four clauses. -/
private theorem foldH_spec (xs : List State) :
    ∀ (V : HashSet State) (F : List State),
      (∀ x, V.contains x = true → (xs.foldl addNewH (V, F)).1.contains x = true) ∧
      (∀ x ∈ xs, (xs.foldl addNewH (V, F)).1.contains x = true) ∧
      (∀ x, (xs.foldl addNewH (V, F)).1.contains x = true →
          V.contains x = true ∨ x ∈ (xs.foldl addNewH (V, F)).2) ∧
      F ⊆ (xs.foldl addNewH (V, F)).2 := by
  induction xs with
  | nil => intro V F; simp; intro x hx; exact Or.inl hx
  | cons y ys ih =>
    intro V F
    simp only [List.foldl_cons]
    by_cases hy : V.contains y = true
    · have : addNewH (V, F) y = (V, F) := by simp [addNewH, hy]
      rw [this]
      obtain ⟨h1, h2, h3, h4⟩ := ih V F
      refine ⟨h1, ?_, h3, h4⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1 _ hy
      · exact h2 x hx
    · have : addNewH (V, F) y = (V.insert y, y :: F) := by simp [addNewH, hy]
      rw [this]
      obtain ⟨h1, h2, h3, h4⟩ := ih (V.insert y) (y :: F)
      have hins : ∀ x, V.contains x = true → (V.insert y).contains x = true := by
        intro x hx; simp [HashSet.contains_insert, hx]
      refine ⟨fun x hx => h1 x (hins x hx), ?_, ?_, fun x hx => h4 (List.mem_cons_of_mem _ hx)⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1 _ (by simp [HashSet.contains_insert])
        · exact h2 x hx
      · intro x hx
        rcases h3 x hx with h | h
        · have h' : (y == x) = true ∨ V.contains x = true := by
            simpa [HashSet.contains_insert] using h
          rcases h' with h' | h'
          · have := eq_of_beq h'; subst this; exact Or.inr (h4 List.mem_cons_self)
          · exact Or.inl h'
        · exact Or.inr h

/-- The BFS invariant for hash sets (same meaning as `Closed`). -/
def ClosedH (L : Level) (V : HashSet State) (F : List State) : Prop :=
  ∀ x, V.contains x = true → x ∈ F ∨ ∀ y ∈ succs L x, V.contains y = true

/-- Hash-set version of `expand_spec`; also records that new states come from the new frontier. -/
private theorem expandH_spec (L : Level) (V : HashSet State) (F : List State) (hc : ClosedH L V F) :
    (∀ x, V.contains x = true → (expandH L V F).1.contains x = true) ∧
    (∀ x ∈ F, ∀ y ∈ succs L x, (expandH L V F).1.contains y = true) ∧
    ClosedH L (expandH L V F).1 (expandH L V F).2 ∧
    (∀ x, (expandH L V F).1.contains x = true → V.contains x = true ∨ x ∈ (expandH L V F).2) := by
  obtain ⟨h1, h2, h3, _⟩ := foldH_spec (F.flatMap (succs L)) V []
  have hfx : ∀ x ∈ F, ∀ y ∈ succs L x, (expandH L V F).1.contains y = true := by
    intro x hx y hy
    exact h2 y (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
  refine ⟨h1, hfx, ?_, h3⟩
  intro x hx
  rcases h3 x hx with h | h
  · rcases hc x h with hF | hS
    · exact Or.inr (hfx x hF)
    · exact Or.inr (fun y hy => h1 y (hS y hy))
  · exact Or.inl h

/-- Two invariants hold after every layer: the BFS invariant, and "if the checker is still
`true` then no visited state is a win". -/
private theorem bfsH_inv (L : Level) (k : Nat) :
    ClosedH L (bfsStateH L k).1 (bfsStateH L k).2.1 ∧
    ((bfsStateH L k).2.2 = true → ∀ x, (bfsStateH L k).1.contains x = true → notWin L x = true) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro x hx; left
      simp only [bfsStateH, HashSet.contains_insert, HashSet.contains_empty] at hx
      have hx' : L.start = x := by simpa using hx
      subst hx'; simp [bfsStateH]
    · intro h x hx
      simp only [bfsStateH, HashSet.contains_insert, HashSet.contains_empty] at hx h
      have hx' : L.start = x := by simpa using hx
      subst hx'; simpa [notWin] using h
  | succ k ih =>
    obtain ⟨hc, hg⟩ := ih
    have hsp := expandH_spec L _ _ hc
    simp only [bfsStateH]
    refine ⟨hsp.2.2.1, ?_⟩
    intro hok x hx
    simp only [Bool.and_eq_true] at hok
    rcases hsp.2.2.2 x hx with h | h
    · exact hg hok.1 x h
    · exact List.all_eq_true.mp hok.2 x h

/-- **Completeness** of the hash-set search (see `reach_mem`). -/
theorem reachH_mem (L : Level) (k : Nat) (s : State) (h : Reach L k s) :
    (bfsStateH L k).1.contains s = true := by
  induction h with
  | start =>
    simp [bfsStateH, HashSet.contains_insert]
  | @stay k s _ ih => exact (expandH_spec L _ _ (bfsH_inv L k).1).1 s ih
  | @move k s a hr ih =>
    have hmem : step L s a ∈ succs L s :=
      List.mem_map.mpr ⟨a, by cases a with | wait => simp [Act.all] | go d => cases d <;> simp [Act.all], rfl⟩
    rcases (bfsH_inv L k).1 s ih with hF | hS
    · exact (expandH_spec L _ _ (bfsH_inv L k).1).2.1 s hF _ hmem
    · exact (expandH_spec L _ _ (bfsH_inv L k).1).1 _ (hS _ hmem)

/-- **Soundness of the fast checker**: a passing search means no short solution exists. -/
theorem no_short_solution_h (L : Level) (k : Nat) (h : bfsNoWinH L k = true) :
    ∀ ms : List Act, ms.length ≤ k → ¬ Solves L ms := by
  intro ms hlen hs
  have hmem := reachH_mem L k _ (reach_mono L hlen (run_reach L ms))
  have := (bfsH_inv L k).2 h _ hmem
  simp only [notWin, decide_eq_true_eq] at this
  exact this hs

end HeartGrid
