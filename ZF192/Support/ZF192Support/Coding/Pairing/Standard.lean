module
public import Std
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Ring.Parity
@[expose] public section

/-! # Cantor pairing and unpairing on the standard natural numbers -/

namespace CCodeSoundness

def cantor (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

theorem cantor_double (a b : Nat) :
    2 * cantor a b = (a + b) * (a + b + 1) + 2 * b := by
  rw [cantor, Nat.mul_add, Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one (a + b))]

private theorem choose_two_succ (s : Nat) :
    (s + 1).choose 2 = s * (s + 1) / 2 := by
  rw [Nat.choose_two_right]
  simp [Nat.mul_comm]

theorem triangular_ge (s : Nat) : s ≤ s * (s + 1) / 2 := by
  rw [← choose_two_succ]
  cases s with
  | zero => simp
  | succ s =>
    rw [Nat.choose_succ_succ' (s + 1) 1, Nat.choose_one_right]
    exact Nat.le_add_right _ _

theorem cantor_ge_left (a b : Nat) : a ≤ cantor a b :=
  (Nat.le_add_right a b).trans ((triangular_ge (a + b)).trans (Nat.le_add_right _ b))

theorem cantor_ge_right (a b : Nat) : b ≤ cantor a b :=
  Nat.le_add_left b _

theorem triangular_succ (s : Nat) :
    (s+1)*(s+1+1)/2 = s*(s+1)/2 + s+1 := by
  rw [← choose_two_succ, Nat.choose_succ_succ' (s + 1) 1, Nat.choose_one_right, choose_two_succ]
  omega

theorem triangular_mono {s t : Nat} (h : s ≤ t) :
    s*(s+1)/2 ≤ t*(t+1)/2 := by
  simpa only [choose_two_succ] using Nat.choose_le_choose 2 (Nat.succ_le_succ h)

theorem cantor_interval (a b : Nat) :
    (a+b)*(a+b+1)/2 ≤ cantor a b ∧
    cantor a b < (a+b+1)*(a+b+1+1)/2 := by
  rw [triangular_succ]
  unfold cantor
  omega

theorem cantor_injective {a b c d : Nat} (he : cantor a b = cantor c d) :
    a = c ∧ b = d := by
  have below {x y u v : Nat} (h : x + y < u + v) : cantor x y < cantor u v :=
    (cantor_interval x y).2.trans_le <|
      (triangular_mono (Nat.succ_le_of_lt h)).trans (cantor_interval u v).1
  have hs : a + b = c + d :=
    le_antisymm (le_of_not_gt fun h => (below h).ne he.symm)
      (le_of_not_gt fun h => (below h).ne he)
  unfold cantor at he
  rw [hs] at he
  omega

def unpair : Nat → Nat × Nat
  | 0 => (0,0)
  | n+1 => let (a,b) := unpair n
           if a=0 then (b+1,0) else (a-1,b+1)

theorem unpair_spec (n : Nat) : cantor (unpair n).1 (unpair n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      generalize he : unpair n = p at *
      obtain ⟨a,b⟩ := p
      simp only [unpair, he]
      by_cases ha : a=0
      · subst a
        simp only [ite_true, cantor, Nat.zero_add, Nat.add_zero] at ih ⊢
        rw [triangular_succ]
        omega
      · simp only [ha, ite_false]
        have hs : a-1+(b+1) = a+b := by omega
        simp only [cantor] at ih ⊢
        rw [hs]
        omega

theorem unpair_left_le (n : Nat) : (unpair n).1 ≤ n := by
  simpa only [unpair_spec] using cantor_ge_left (unpair n).1 (unpair n).2

theorem unpair_right_le (n : Nat) : (unpair n).2 ≤ n := by
  simpa only [unpair_spec] using cantor_ge_right (unpair n).1 (unpair n).2

end CCodeSoundness
