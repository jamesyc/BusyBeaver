module
public import I3_334Support.Machine
@[expose] public section

namespace PalomarI3380

/-- A tape window with a specified number of known cells on each side.
The right side includes the scanned cell when its length is positive. -/
structure DecoderWindow where
  config : Configuration
  leftLength : Nat
  rightLength : Nat
  deriving DecidableEq, Repr

namespace DecoderWindow

def embed (w : DecoderWindow) (leftTail rightTail : Nat) : Configuration :=
  ⟨w.config.state, w.config.left + 2 ^ w.leftLength * leftTail,
    w.config.right + 2 ^ w.rightLength * rightTail⟩

def next (m : Machine) (w : DecoderWindow) : Option DecoderWindow :=
  match w.rightLength with
  | 0 => none
  | r + 1 =>
    if m.row w.config.state (w.config.right % 2) % 2 = 1 then
      (step m w.config).map (fun c => ⟨c, w.leftLength + 1, r⟩)
    else
      match w.leftLength with
      | 0 => none
      | l + 1 => (step m w.config).map (fun c => ⟨c, l, r + 2⟩)

private theorem read_bit (bits len tail : Nat) :
    (bits + 2 ^ (len + 1) * tail) % 2 = bits % 2 := by
  rw [Nat.pow_succ', Nat.mul_assoc, Nat.add_mul_mod_self_left]

private theorem drop_bit (bits len tail : Nat) :
    (bits + 2 ^ (len + 1) * tail) / 2 = bits / 2 + 2 ^ len * tail := by
  rw [Nat.pow_succ', Nat.mul_assoc, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

/-- A successful window step works with arbitrary bits on either side. -/
theorem step_embed {m : Machine} {w out : DecoderWindow} (h : next m w = some out)
    (leftTail rightTail : Nat) :
    step m (w.embed leftTail rightTail) = some (out.embed leftTail rightTail) := by
  rcases w with ⟨⟨q, left, right⟩, l, r⟩
  cases r with
  | zero => simp [next] at h
  | succ r =>
    by_cases hState : m.workingStates ≤ q
    · cases l <;> simp [next, step, hState] at h
    have hRight := read_bit right r rightTail
    have hDropRight := drop_bit right r rightTail
    by_cases hMove : m.row q (right % 2) % 2 = 1
    · simp only [next, hMove, ↓reduceIte, step, hState, Option.map_some,
        Option.some.injEq] at h
      subst out
      simp only [embed, step, hRight, hDropRight, hState, hMove, ↓reduceIte,
        Option.some.injEq, Configuration.mk.injEq, true_and]
      simp only [Nat.pow_succ', Nat.mul_add, Nat.mul_assoc]
      rw [and_true, Nat.add_right_comm]
    · cases l with
      | zero => simp [next, hMove] at h
      | succ l =>
        simp only [next, hMove, ↓reduceIte, step, hState, Option.map_some,
          Option.some.injEq] at h
        subst out
        simp only [embed, step, hRight, hDropRight, read_bit left l leftTail,
          drop_bit left l leftTail, hState, hMove, ↓reduceIte, Option.some.injEq,
          Configuration.mk.injEq, true_and]
        simp only [Nat.pow_succ', Nat.mul_assoc, Nat.mul_add]
        omega

/-- Search a fixed local window for the specified exit. A transition that
would inspect an unknown cell makes the search fail. -/
def runToMatch (m : Machine) (goal : DecoderWindow) : Nat → DecoderWindow → Option Nat
  | 0, w => if w = goal then some 0 else none
  | fuel + 1, w =>
    if w = goal then some 0 else do
      let nextWindow ← next m w
      let steps ← runToMatch m goal fuel nextWindow
      return steps + 1

theorem runToMatch_sound {m : Machine} {w goal : DecoderWindow} {fuel steps : Nat}
    (h : runToMatch m goal fuel w = some steps) (leftTail rightTail : Nat) :
    run m steps (w.embed leftTail rightTail) = some (goal.embed leftTail rightTail) := by
  induction fuel generalizing w steps with
  | zero =>
    by_cases heq : w = goal <;> simp [runToMatch, heq] at h
    simp [h.symm, heq, run]
  | succ fuel ih =>
    by_cases heq : w = goal
    · simp [runToMatch, heq] at h
      simp [h.symm, heq, run]
    · cases hs : next m w with
      | none => simp [runToMatch, heq, hs] at h
      | some w' =>
        cases hr : runToMatch m goal fuel w' with
        | none => simp [runToMatch, heq, hs, hr] at h
        | some n =>
          simp [runToMatch, heq, hs, hr] at h
          subst steps
          rw [run, step_embed hs]
          exact ih hr

theorem embed_previous (w : DecoderWindow) (h : 0 < w.leftLength) (leftTail rightTail : Nat) :
    (w.embed leftTail rightTail).left % 2 = w.config.left % 2 := by
  rcases w with ⟨c, n, r⟩
  cases n with
  | zero => contradiction
  | succ n => exact read_bit c.left n leftTail

end DecoderWindow
end PalomarI3380
