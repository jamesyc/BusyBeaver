module
public import Std
@[expose] public section

namespace PalomarI3380

/-- Each natural encodes one side of the tape, with the closest bit least
significant. The scanned cell is the least significant bit of `right`. -/
structure Configuration where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def blank : Configuration := ⟨0, 0, 0⟩

/-- Rows are ordered by working state, then by read bit. Each 11-bit row
stores `4 * next + 2 * write + direction`, with right = 1. Packing permits
constant-index arithmetic lookup during kernel replay. -/
structure Machine where
  workingStates : Nat
  packedRows : Nat

def Machine.row (m : Machine) (state read : Nat) : Nat :=
  (m.packedRows >>> (11 * (2 * state + read))) % 2048

def step (m : Machine) (c : Configuration) : Option Configuration :=
  if m.workingStates ≤ c.state then none else
    let row := m.row c.state (c.right % 2)
    let written := row / 2 % 2
    let next := row / 4
    let tail := c.right / 2
    if row % 2 = 1 then
      some ⟨next, 2 * c.left + written, tail⟩
    else
      some ⟨next, c.left / 2, 4 * tail + 2 * written + c.left % 2⟩

def run (m : Machine) : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => match step m c with
    | some next => run m n next
    | none => none

theorem run_add (machine : Machine) (m n : Nat) (c : Configuration) :
    run machine (m + n) c = (run machine m c).bind (run machine n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
      rw [Nat.succ_add, run, run]
      cases h : step machine c with
      | none => rfl
      | some next => exact ih next

theorem join_run {machine : Machine} {a b c : Configuration} {m n : Nat}
    (first : run machine m a = some b) (second : run machine n b = some c) :
    run machine (m + n) a = some c := by
  rw [run_add, first]
  exact second

/-- A successful run in the smaller table is preserved by a table that
agrees at every state read during that run. The final state may lie outside
the smaller table. -/
theorem run_extend {small large : Machine}
    (stateBound : small.workingStates ≤ large.workingStates)
    (sameRows : ∀ q, q < small.workingStates → ∀ b, b < 2 →
        large.row q b = small.row q b)
    {n : Nat} {c d : Configuration} (h : run small n c = some d) :
    run large n c = some d := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    have hValid : c.state < small.workingStates := by
      by_cases hq : small.workingStates ≤ c.state
      · simp [run, step, hq] at h
      · omega
    have stepEq : step large c = step small c := by
      have hqSmall : ¬small.workingStates ≤ c.state := by omega
      have hqLarge : ¬large.workingStates ≤ c.state := by omega
      simp only [step, hqSmall, hqLarge, ↓reduceIte,
        sameRows c.state hValid (c.right % 2) (Nat.mod_lt _ (by decide))]
    rw [run, stepEq]
    rw [run] at h
    cases hs : step small c with
    | none => simp [hs] at h
    | some next =>
      apply ih
      simpa only [hs] using h

end PalomarI3380
