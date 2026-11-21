module
public import I0451.Simulation

/-! Interpretation of the packed tape as a doubly infinite array of bits
with coordinates relative to the head. -/

@[expose] public section
namespace I0451

/-- A cell at an integer offset from the head, which is at offset zero. -/
def Config.cell (c : Config) : Int → Bool
  | .ofNat n => c.right.testBit n
  | .negSucc n => c.left.testBit n

private theorem bit_zero (n : Nat) : n.testBit 0 = bit n := by
  rw [Nat.testBit_zero]
  cases h : bit n
  · have notOne : n % 2 ≠ 1 := fun one => by simp [bit, one] at h
    simp [notOne]
  · have one : n % 2 = 1 := by simpa only [bit, beq_iff_eq] using h
    simp [one]

private theorem push_zero (b : Bool) (n : Nat) : (push b n).testBit 0 = b := by
  rw [bit_zero, bit_push]

private theorem push_succ (b : Bool) (n i : Nat) :
    (push b n).testBit (i + 1) = n.testBit i := by
  rw [Nat.testBit_add_one, pop_push]

/-- A physical move overwrites the old head cell and shifts the coordinate
system one cell in the specified direction. All other cells are preserved. -/
theorem move_cell (code l r : Nat) (i : Int) :
    let delta : Int := if bit (code / 2) then 1 else -1
    (move code l r).cell i =
      if i + delta = 0 then bit code else (Config.mk 0 l r).cell (i + delta) := by
  have positive (j : Nat) : Int.ofNat (j + 1) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
  cases direction : bit (code / 2)
  · simp only [move, direction, Bool.false_eq_true, ite_false]
    cases i with
    | ofNat i =>
      rcases i with _ | _ | i
      · change (push (bit l) (push (bit code) (r / 2))).testBit 0 = l.testBit 0
        rw [push_zero, bit_zero]
      · change (push (bit l) (push (bit code) (r / 2))).testBit 1 = bit code
        rw [push_succ (i := 0), push_zero]
      · have shift : Int.ofNat (i + 2) + -1 = Int.ofNat (i + 1) := by
          simp only [Int.ofNat_eq_natCast]
          omega
        rw [shift, ite_eq_right (positive i)]
        simp [Config.cell, push_succ, Nat.testBit_div_two]
    | negSucc i =>
      have shift : (Int.negSucc i) + -1 = Int.negSucc (i + 1) := by omega
      rw [shift]
      simp [Config.cell, Nat.testBit_div_two]
  · simp only [move, direction, ite_true]
    cases i with
    | ofNat i =>
      have shift : Int.ofNat i + 1 = Int.ofNat (i + 1) := rfl
      rw [shift, ite_eq_right (positive i)]
      simp [Config.cell, Nat.testBit_div_two]
    | negSucc i =>
      cases i with
      | zero =>
        change (push (bit code) l).testBit 0 = bit code
        exact push_zero _ _
      | succ i =>
        have shift : (Int.negSucc (i + 1)) + 1 = Int.negSucc i := by omega
        rw [shift]
        simp [Config.cell, push_succ]

end I0451
