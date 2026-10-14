import HeartGrid.Rules
/-!
# A verified breadth-first search

`bfsNoWin L k = true` implies that **no** sequence of at most `k` moves solves `L`.
This is the lower-bound half of "level `L` needs exactly `n` moves".
The theorem is proved once, for every level; per level only the (decidable) check is run.
-/
namespace HeartGrid

/-- The five states reachable in one action (some may equal the current state). -/
def succs (L : Level) (s : State) : List State := Act.all.map (step L s)

/-- The fold body of `expand`: record `x` as visited and as frontier if it is new. -/
def addNew (acc : List State × List State) (x : State) : List State × List State :=
  if x ∈ acc.1 then acc else (x :: acc.1, x :: acc.2)

/-- One BFS layer.  Expand every frontier state; return the enlarged visited list together with the
new frontier (the successors not seen before). -/
def expand (L : Level) (V F : List State) : List State × List State :=
  (F.flatMap (succs L)).foldl addNew (V, [])

/-- Visited list and frontier after `k` layers of search from the starting state. -/
def bfsState (L : Level) : Nat → List State × List State
  | 0 => ([L.start], [L.start])
  | k + 1 => expand L (bfsState L k).1 (bfsState L k).2

/-- The checker: `true` when no state within `k` actions of the start is a win.
It is an ordinary computable function, so a particular level can be checked by evaluating it. -/
def bfsNoWin (L : Level) (k : Nat) : Bool :=
  (bfsState L k).1.all fun s => decide (s.player ≠ L.exit)

/-! ### Proof -/

/-- What the fold inside `expand` guarantees, by induction on the list `xs` of successors:
nothing visited is forgotten; every successor ends up visited; anything visited was either
already visited or is on the new frontier; and the old frontier is kept. -/
private theorem fold_spec (xs : List State) :
    ∀ (V F : List State),
      V ⊆ (xs.foldl addNew (V, F)).1 ∧
      (∀ x ∈ xs, x ∈ (xs.foldl addNew (V, F)).1) ∧
      (∀ x ∈ (xs.foldl addNew (V, F)).1, x ∈ V ∨ x ∈ (xs.foldl addNew (V, F)).2) ∧
      F ⊆ (xs.foldl addNew (V, F)).2 := by
  induction xs with
  | nil => intro V F; simp; intro x hx; exact Or.inl hx
  | cons y ys ih =>
    intro V F
    simp only [List.foldl_cons]
    by_cases hy : y ∈ V
    · have : addNew (V, F) y = (V, F) := by simp [addNew, hy]
      rw [this]
      obtain ⟨h1, h2, h3, h4⟩ := ih V F
      refine ⟨h1, ?_, h3, h4⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1 hy
      · exact h2 x hx
    · have : addNew (V, F) y = (y :: V, y :: F) := by simp [addNew, hy]
      rw [this]
      obtain ⟨h1, h2, h3, h4⟩ := ih (y :: V) (y :: F)
      refine ⟨fun x hx => h1 (List.mem_cons_of_mem _ hx), ?_, ?_,
        fun x hx => h4 (List.mem_cons_of_mem _ hx)⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1 List.mem_cons_self
        · exact h2 x hx
      · intro x hx
        rcases h3 x hx with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (h4 List.mem_cons_self)
          · exact Or.inl h
        · exact Or.inr h

/-- The BFS invariant.  Every visited state is either on the frontier, or all of its successors
have been visited already.  (So the search has no "loose ends" except the frontier.) -/
def Closed (L : Level) (V F : List State) : Prop :=
  ∀ x ∈ V, x ∈ F ∨ ∀ y ∈ succs L x, y ∈ V

/-- One layer preserves the invariant, keeps everything visited, and visits every successor of
every frontier state. -/
private theorem expand_spec (L : Level) (V F : List State) (hc : Closed L V F) :
    V ⊆ (expand L V F).1 ∧
    (∀ x ∈ F, ∀ y ∈ succs L x, y ∈ (expand L V F).1) ∧
    Closed L (expand L V F).1 (expand L V F).2 := by
  obtain ⟨h1, h2, h3, _⟩ := fold_spec (F.flatMap (succs L)) V []
  have hfx : ∀ x ∈ F, ∀ y ∈ succs L x, y ∈ (expand L V F).1 := by
    intro x hx y hy
    exact h2 y (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
  refine ⟨h1, hfx, ?_⟩
  intro x hx
  rcases h3 x hx with h | h
  · rcases hc x h with hF | hS
    · exact Or.inr (hfx x hF)
    · exact Or.inr (fun y hy => h1 (hS y hy))
  · exact Or.inl h

/-- The invariant holds after any number of layers (induction on the layer count). -/
private theorem bfsState_closed (L : Level) (k : Nat) :
    Closed L (bfsState L k).1 (bfsState L k).2 := by
  induction k with
  | zero => intro x hx; exact Or.inl hx
  | succ k ih => exact (expand_spec L _ _ ih).2.2

/-- `Reach L k s`: state `s` can be reached from the start in at most `k` actions.
This is the semantic notion the search must cover. -/
inductive Reach (L : Level) : Nat → State → Prop
  | start : Reach L 0 L.start
  | stay {k s} : Reach L k s → Reach L (k + 1) s
  | move {k s} (a : Act) : Reach L k s → Reach L (k + 1) (step L s a)

/-- **Completeness**: every state reachable within `k` actions is in the visited list after `k` layers.
Proof by induction on `Reach`: a successor of a frontier state is visited by `expand_spec`, and a
successor of a non-frontier state was visited already because of the invariant. -/
private theorem reach_mem (L : Level) (k : Nat) (s : State) (h : Reach L k s) :
    s ∈ (bfsState L k).1 := by
  induction h with
  | start => simp [bfsState]
  | @stay k s _ ih => exact (expand_spec L _ _ (bfsState_closed L k)).1 ih
  | @move k s d hr ih =>
    rcases bfsState_closed L k s ih with hF | hS
    · exact (expand_spec L _ _ (bfsState_closed L k)).2.1 s hF _
        (List.mem_map.mpr ⟨d, by cases d with | wait => simp [Act.all] | go d => cases d <;> simp [Act.all], rfl⟩)
    · have := hS (step L s d) (List.mem_map.mpr ⟨d, by cases d with | wait => simp [Act.all] | go d => cases d <;> simp [Act.all], rfl⟩)
      exact (expand_spec L _ _ (bfsState_closed L k)).1 this

/-- Running a list followed by one more action is one more `step`. -/
theorem run_append (L : Level) (s : State) (ms : List Act) (d : Act) :
    run L s (ms ++ [d]) = step L (run L s ms) d := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp [run, ih]

/-- Helper for `run_reach`, by induction on the length of the action list. -/
theorem run_reach_aux (L : Level) :
    ∀ (n : Nat) (ms : List Act), ms.length = n → Reach L n (run L L.start ms) := by
  intro n
  induction n with
  | zero => intro ms h; rw [List.length_eq_zero_iff.mp h]; exact Reach.start
  | succ n ih =>
    intro ms h
    have hne : ms ≠ [] := by intro e; simp [e] at h
    have hsplit := List.dropLast_concat_getLast hne
    rw [← hsplit, run_append]
    exact Reach.move _ (ih _ (by simp [List.length_dropLast, h]))

/-- Playing `n` actions from the start reaches a state that is `Reach`able within `n` actions. -/
theorem run_reach (L : Level) (ms : List Act) :
    Reach L ms.length (run L L.start ms) := run_reach_aux L _ ms rfl

/-- Reachable within `j` actions implies reachable within any larger `k`. -/
theorem reach_mono (L : Level) {j k : Nat} (hjk : j ≤ k) {s : State}
    (h : Reach L j s) : Reach L k s := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact Reach.stay ih

/-- **Soundness of the checker**: a passing search means no short solution exists. -/
theorem no_short_solution (L : Level) (k : Nat) (h : bfsNoWin L k = true) :
    ∀ ms : List Act, ms.length ≤ k → ¬ Solves L ms := by
  intro ms hlen hs
  have hmem := reach_mem L k _ (reach_mono L hlen (run_reach L ms))
  unfold bfsNoWin at h
  have := List.all_eq_true.mp h _ hmem
  simp only [decide_eq_true_eq] at this
  exact this hs

end HeartGrid
