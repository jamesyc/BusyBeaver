module
public import I0451.Simulation

@[expose] public section
namespace I0451

theorem push_bit_pop (n : Nat) : push (bit n) (n / 2) = n := by
  have parity : (bit n).toNat = n % 2 := by
    cases h : bit n
    · have even : n % 2 ≠ 1 := fun odd => by simp [bit, odd] at h
      simp only [Bool.toNat_false]
      omega
    · have odd : n % 2 = 1 := by simpa only [bit, beq_iff_eq] using h
      simp only [Bool.toNat_true, odd]
  unfold push
  omega

/-- Known tape cells around the head; all cells outside the window are arbitrary. -/
structure Window where
  state : Nat
  left : List Bool
  right : List Bool
  deriving DecidableEq, Repr

def Window.extend (window : Window) (left right : Nat) : Config :=
  ⟨window.state, window.left.foldr push left, window.right.foldr push right⟩

def Window.step (table : Table) (window : Window) : Option Window := do
  let (read :: right) := window.right | none
  let (code + 1) := row table window.state read | none
  if bit (code / 2) then
    return ⟨code / 4, bit code :: window.left, right⟩
  else
    let (cell :: left) := window.left | none
    return ⟨code / 4, left, cell :: bit code :: right⟩

def Window.run (table : Table) : Nat → Window → Option Window
  | 0, window => some window
  | n + 1, window => (window.step table).bind (Window.run table n)

theorem Window.step_extend {table : Table} {a b : Window}
    (result : a.step table = some b) (left right : Nat) :
    I0451.step table (a.extend left right) = some (b.extend left right) := by
  obtain ⟨q, l, r⟩ := a
  cases r with
  | nil => simp [Window.step] at result
  | cons read r =>
    cases h : row table q read with
    | zero => simp [Window.step, h] at result
    | succ code =>
      cases direction : bit (code / 2)
      · cases l with
        | nil => simp [Window.step, h, direction] at result
        | cons cell l =>
          simp [Window.step, h, direction] at result
          subst b
          simp [Window.extend, I0451.step, h, move, direction]
      · simp [Window.step, h, direction] at result
        subst b
        simp [Window.extend, I0451.step, h, move, direction]

theorem Window.run_extend {table : Table} {a b : Window} {n : Nat}
    (result : a.run table n = some b) (left right : Nat) :
    I0451.run table n (a.extend left right) = some (b.extend left right) := by
  induction n generalizing a with
  | zero =>
    simp [Window.run] at result
    subst b
    rfl
  | succ n ih =>
    cases h : a.step table with
    | none => simp [Window.run, h] at result
    | some next =>
      rw [I0451.run, Window.step_extend h]
      exact ih (by simpa [Window.run, h] using result)

/-- The window starts on its only known right cell and can also read up
to two known cells to its left. -/
def Window.seed (q : Nat) (a b read : Bool) : Window :=
  ⟨q, [a, b], [read]⟩

theorem Window.extend_seed (q : Nat) (a b : Bool) (left right : Nat) :
    (Window.seed q a b (bit right)).extend left (right / 2) =
      ⟨q, push a (push b left), right⟩ := by
  simp [Window.seed, Window.extend, push_bit_pop]

end I0451
