/-!
# HeartGrid rules

A Lolo-style grid puzzle.  The player collects every heart, which opens the exit door,
then walks through it into the next room.  Emerald blocks can be pushed one at a time;
a block pushed into water fills it, and both disappear (a bridge).

Enemies take a turn after every move or wait of the player:
* **patrollers** walk the way they face and turn round when blocked;
* **hunters** patrol too, but chase along a clear row or column once they see the player.
Touching an enemy is fatal (`dead`), whoever walks into whom.

Mirrored by `tools/rules.py`, `tools/solve.cpp` and `web/engine.js`.
-/
namespace HeartGrid

/-- A board position `(row, column)`, counted from the top-left corner, starting at 0. -/
abbrev Pos := Nat × Nat

/-- The four compass directions: up, down, left, right (row 0 is the top row). -/
inductive Dir | U | D | L | R
  deriving DecidableEq, Repr, Hashable

/-- The opposite direction; patrolling enemies use it to turn round. -/
def Dir.opp : Dir → Dir
  | .U => .D | .D => .U | .L => .R | .R => .L

/-- One player action.  `go d` tries to step in direction `d`;
`wait` lets the enemies take a turn while the player stays put. -/
inductive Act | go (d : Dir) | wait
  deriving DecidableEq, Repr

/-- Every action; the search tries each of them from each state. -/
def Act.all : List Act := [.go .U, .go .D, .go .L, .go .R, .wait]

/-- A roaming enemy. -/
structure Enemy where
  /-- Where it is standing. -/
  pos : Pos
  /-- The way it is facing, and therefore walking when it patrols. -/
  dir : Dir
  /-- `true` for a hunter (chases when it sees the player), `false` for a plain patroller. -/
  hunter : Bool
  deriving DecidableEq, Repr, Hashable

/-- Everything that changes during play.  Walls and the door never move, so they live in `Level`. -/
structure State where
  /-- The player's position. -/
  player  : Pos
  /-- Emerald blocks, kept sorted by `key` so equal boards are equal states. -/
  blocks  : List Pos
  /-- Hearts still to collect.  The door opens when this is empty. -/
  hearts  : List Pos
  /-- Water cells not yet bridged. -/
  water   : List Pos
  /-- Enemies, in a fixed order; they move one after another in this order. -/
  enemies : List Enemy
  /-- Set once an enemy and the player meet.  A dead state never changes again. -/
  dead    : Bool
  deriving DecidableEq, Repr, Hashable

/-- A room: the fixed scenery plus the starting `State`. -/
structure Level where
  /-- Number of rows. -/
  h : Nat
  /-- Number of columns. -/
  w : Nat
  /-- Wall cells, including the entrance arch the player came in by. -/
  walls : List Pos
  /-- The exit door.  It is impassable until every heart is collected. -/
  exit : Pos
  /-- The state when the player enters the room. -/
  start : State

/-- How many cells away (counting the cell between) a hunter can see along a clear row or column. -/
def sight : Nat := 6

/-- The neighbouring cell in a direction, or `none` when that would fall off the top or left edge. -/
def nudge : Dir → Pos → Option Pos
  | .U, (r, c) => if r = 0 then none else some (r - 1, c)
  | .D, (r, c) => some (r + 1, c)
  | .L, (r, c) => if c = 0 then none else some (r, c - 1)
  | .R, (r, c) => some (r, c + 1)

/-- Is `p` inside the board? -/
def Level.inBounds (L : Level) (p : Pos) : Prop := p.1 < L.h ∧ p.2 < L.w

instance (L : Level) (p : Pos) : Decidable (L.inBounds p) := by
  unfold Level.inBounds; infer_instance

/-- A sort key: row-major order, assuming fewer than 256 columns. -/
def key (p : Pos) : Nat := p.1 * 256 + p.2

/-- Insert into a list already sorted by `key`. -/
def insSorted (x : Pos) : List Pos → List Pos
  | [] => [x]
  | y :: ys => if key x ≤ key y then x :: y :: ys else y :: insSorted x ys

/-- Cells currently occupied by enemies. -/
def State.enemyPos (s : State) : List Pos := s.enemies.map (·.pos)

/-! ### The player's move -/

/-- A block may not be pushed onto `u` if it is off the board, a wall, the door,
another block, a heart, or an enemy.  (Water is fine: the block fills it.) -/
def Level.blocked (L : Level) (s : State) (u : Pos) : Prop :=
  ¬ L.inBounds u ∨ u ∈ L.walls ∨ u = L.exit ∨ u ∈ s.blocks ∨ u ∈ s.hearts ∨ u ∈ s.enemyPos

instance (L : Level) (s : State) (u : Pos) : Decidable (L.blocked s u) := by
  unfold Level.blocked; infer_instance

/-- The state after the player's own move, *before* the enemies act; `none` if the move is blocked.

* walls, water and the board edge block the player;
* the door blocks until no hearts remain, then lets the player through;
* walking into a block pushes it one cell if the cell behind is free (see `Level.blocked`),
  and if that cell is water the block and the water both vanish;
* walking onto a heart collects it;
* walking onto an enemy is fatal. -/
def playerMove (L : Level) (s : State) (d : Dir) : Option State :=
  match nudge d s.player with
  | none => none
  | some t =>
    if ¬ L.inBounds t ∨ t ∈ L.walls ∨ t ∈ s.water then none
    else if t = L.exit then
      (if s.hearts = [] then some { s with player := t } else none)
    else if t ∈ s.blocks then
      match nudge d t with
      | none => none
      | some u =>
        if L.blocked s u then none
        else if u ∈ s.water then
          some { s with player := t, blocks := s.blocks.erase t, water := s.water.erase u }
        else
          some { s with player := t, blocks := insSorted u (s.blocks.erase t) }
    else
      some { s with player := t, hearts := s.hearts.erase t, dead := decide (t ∈ s.enemyPos) }

/-! ### The enemies' turn -/

/-- If `a` and `b` share a row or column, the direction from `a` towards `b` and the cells
strictly between them; otherwise `none`. -/
def lineBetween (a b : Pos) : Option (Dir × List Pos) :=
  if a = b then none
  else if a.1 = b.1 then
    if a.2 < b.2 then some (.R, (List.range' (a.2 + 1) (b.2 - a.2 - 1)).map (a.1, ·))
    else some (.L, (List.range' (b.2 + 1) (a.2 - b.2 - 1)).map (a.1, ·))
  else if a.2 = b.2 then
    if a.1 < b.1 then some (.D, (List.range' (a.1 + 1) (b.1 - a.1 - 1)).map (·, a.2))
    else some (.U, (List.range' (b.1 + 1) (a.1 - b.1 - 1)).map (·, a.2))
  else none

/-- The direction in which a hunter standing at `a` sees the player, if it does:
player in the same row or column, closer than `sight`, with only open floor (no wall, block or door)
in between.  Water does not block the view. -/
def sees (L : Level) (s : State) (a : Pos) : Option Dir :=
  match lineBetween a s.player with
  | none => none
  | some (d, cells) =>
    if cells.length < sight ∧ cells.all (fun q => decide (q ∉ L.walls ∧ q ∉ s.blocks ∧ q ≠ L.exit))
    then some d else none

/-- One enemy's move, given the positions of all the *other* enemies.

A hunter that sees the player turns to face them and steps towards them.  Anything else steps in
the direction it faces, or turns round (without moving) if that cell is not free.  A cell is free
if it is on the board and is not a wall, water, a block, the door or another enemy; the player's
cell counts as free, which is how enemies catch you. -/
def enemyStep (L : Level) (s : State) (others : List Pos) (e : Enemy) : Enemy :=
  let free : Pos → Bool := fun q =>
    decide (L.inBounds q ∧ q ∉ L.walls ∧ q ∉ s.water ∧ q ∉ s.blocks ∧ q ≠ L.exit ∧ q ∉ others)
  let chase : Option Dir := if e.hunter then sees L s e.pos else none
  match chase with
  | some d =>
    match nudge d e.pos with
    | some q => if free q then { e with pos := q, dir := d } else { e with dir := d }
    | none => { e with dir := d }
  | none =>
    match nudge e.dir e.pos with
    | some q => if free q then { e with pos := q } else { e with dir := e.dir.opp }
    | none => { e with dir := e.dir.opp }

/-- Move the enemies one after another.  `done` holds those already moved (reversed) and the
list argument those still to go, so each enemy sees up-to-date positions for the others.
If one lands on the player the player is dead and the rest stay put. -/
def moveEnemies (L : Level) (s : State) : List Enemy → List Enemy → State
  | done, [] => { s with enemies := done.reverse }
  | done, e :: rest =>
    let e' := enemyStep L s (done.map (·.pos) ++ rest.map (·.pos)) e
    if e'.pos = s.player then { s with enemies := done.reverse ++ e' :: rest, dead := true }
    else moveEnemies L s (e' :: done) rest

/-- The enemies' turn: all enemies move, in order. -/
def worldTurn (L : Level) (s : State) : State := moveEnemies L s [] s.enemies

/-! ### One action -/

/-- Apply one player action.

Nothing happens once the player is dead or has left through the door.  Waiting passes a turn.
A blocked move does nothing at all (it is not a turn, so enemies do not move).  A successful move
ends the turn with the enemies moving, unless the player just won or just died. -/
def step (L : Level) (s : State) : Act → State
  | a =>
    if s.dead ∨ s.player = L.exit then s else
    match a with
    | .wait => worldTurn L s
    | .go d =>
      match playerMove L s d with
      | none => s
      | some n => if n.player = L.exit ∨ n.dead then n else worldTurn L n

/-- Play a whole list of actions from a given state. -/
def run (L : Level) : State → List Act → State
  | s, [] => s
  | s, a :: as => run L (step L s a) as

/-- The player has reached the door (which only opens once all hearts are collected). -/
def Level.won (L : Level) (s : State) : Prop := s.player = L.exit

/-- `ms` is a winning sequence of actions for `L`: starting from the entrance, it ends at the door. -/
def Solves (L : Level) (ms : List Act) : Prop := L.won (run L L.start ms)

instance (L : Level) (ms : List Act) : Decidable (Solves L ms) := by
  unfold Solves Level.won; infer_instance

end HeartGrid
