module
public import I3_334Support.Equations.WordCode
@[expose] public section

namespace PalomarI3380.Cantor

/-- Closed triangular number used by the executable decoder. -/
def diagonalStart (n : Nat) : Nat := n * (n + 1) / 2

theorem diagonalStart_eq (n : Nat) : diagonalStart n = triangle n := by
  unfold diagonalStart
  rw [← triangle_twice, Nat.mul_comm 2, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem diagonalStart_succ (n : Nat) :
    diagonalStart (n + 1) = diagonalStart n + (n + 1) := by
  rw [diagonalStart_eq, diagonalStart_eq, triangle]

theorem diagonalStart_lower (n : Nat) : n ≤ diagonalStart n := by
  cases n with
  | zero => decide
  | succ n =>
    rw [diagonalStart_succ]
    exact Nat.le_add_left _ _

/-- Binary search for the diagonal containing the code. The interval
width is a fuel bound, while balanced splitting gives logarithmic depth. -/
def locate (code : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo
    else
      let mid := (lo + hi + 1) / 2
      if diagonalStart mid ≤ code then locate code fuel mid hi
      else locate code fuel lo (mid - 1)

theorem locate_spec (code fuel lo hi : Nat) (hOrder : lo ≤ hi)
    (hLower : diagonalStart lo ≤ code) (hUpper : code < diagonalStart (hi + 1))
    (hFuel : hi - lo ≤ fuel) :
    diagonalStart (locate code fuel lo hi) ≤ code ∧
      code < diagonalStart (locate code fuel lo hi + 1) := by
  induction fuel generalizing lo hi with
  | zero =>
    have heq : hi = lo := by omega
    subst hi
    exact ⟨hLower, hUpper⟩
  | succ fuel ih =>
    by_cases heq : hi ≤ lo
    · have hh : hi = lo := by omega
      subst hi
      simpa only [locate, Nat.le_refl, ↓reduceIte] using And.intro hLower hUpper
    · let mid := (lo + hi + 1) / 2
      have hlt : lo < mid := by dsimp only [mid]; omega
      have hle : mid ≤ hi := by dsimp only [mid]; omega
      by_cases hmid : diagonalStart mid ≤ code
      · have hr := ih mid hi hle hmid hUpper (by omega)
        simpa only [locate, heq, ↓reduceIte, show diagonalStart ((lo + hi + 1) / 2) ≤ code from hmid] using hr
      · have hBound : code < diagonalStart (mid - 1 + 1) := by
          have hNat : mid - 1 + 1 = mid := by omega
          rw [hNat]
          omega
        have hr := ih lo (mid - 1) (by omega) hLower hBound (by omega)
        simpa only [locate, heq, ↓reduceIte,
          show ¬diagonalStart ((lo + hi + 1) / 2) ≤ code from hmid] using hr

def unpair (n : Nat) : Nat × Nat :=
  let sum := locate n n 0 n
  let second := n - diagonalStart sum
  (sum - second, second)

theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n := by
  let sum := locate n n 0 n
  let base := diagonalStart sum
  let y := n - base
  have hs := locate_spec n n 0 n (Nat.zero_le _) (by change 0 ≤ n; omega)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (diagonalStart_lower (n + 1))) (by omega)
  change base ≤ n ∧ n < diagonalStart (sum + 1) at hs
  have hUpper := hs.2
  rw [diagonalStart_succ] at hUpper
  have hSum : sum - y + y = sum := by dsimp only [base, y] at *; omega
  change pair (sum - y) y = n
  rw [pair_as_triangle, hSum, ← diagonalStart_eq]
  dsimp only [base, y] at *
  omega

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have h := pair_eq (pair_unpair (pair a b))
  exact Prod.ext h.1 h.2

theorem right_lt_of_left_pos {a : Nat} (h : 0 < a) (b : Nat) : b < pair a b := by
  have ht := diagonalStart_lower (a + b)
  rw [diagonalStart_eq] at ht
  rw [pair_as_triangle]
  omega

/-- One iteration of the release's two-register unpair loop. -/
def advance (p : Nat × Nat) : Nat × Nat :=
  if p.1 = 0 then (p.2 + 1, 0) else (p.1 - 1, p.2 + 1)

theorem pair_advance (p : Nat × Nat) :
    pair (advance p).1 (advance p).2 = pair p.1 p.2 + 1 := by
  rcases p with ⟨a, b⟩
  cases a with
  | zero =>
    simp only [advance, ↓reduceIte, pair_as_triangle, Nat.add_zero, Nat.zero_add, triangle]
    omega
  | succ a =>
    simp only [advance, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, pair_as_triangle]
    have sum : a + (b + 1) = a + 1 + b := by omega
    rw [sum]
    omega

def advanceLoop : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p => advanceLoop n (advance p)

theorem advanceLoop_code (n : Nat) (p : Nat × Nat) :
    let out := advanceLoop n p
    pair out.1 out.2 = pair p.1 p.2 + n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [advanceLoop]
    have h := ih (advance p)
    simp only [pair_advance] at h
    dsimp only
    rw [h]
    omega

/-- The two outputs of the literal unpair register loop. -/
theorem advanceLoop_unpair (n : Nat) : advanceLoop n (0, 0) = unpair n := by
  have h := advanceLoop_code n (0, 0)
  have codeZero : pair 0 0 = 0 := rfl
  rw [codeZero, Nat.zero_add] at h
  have same := pair_eq (h.trans (pair_unpair n).symm)
  exact Prod.ext same.1 same.2

end PalomarI3380.Cantor
