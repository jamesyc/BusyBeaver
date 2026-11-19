module
public import CantorInverse
@[expose] public section
namespace C207Soundness

theorem triangular_mono {s t : Nat} (h : s ≤ t) :
    s*(s+1)/2 ≤ t*(t+1)/2 := by
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem cantor_interval (a b : Nat) :
    (a+b)*(a+b+1)/2 ≤ cantor a b ∧
    cantor a b < (a+b+1)*(a+b+1+1)/2 := by
  rw [triangular_succ]
  unfold cantor
  omega

theorem cantor_injective {a b c d : Nat} (he : cantor a b = cantor c d) :
    a = c ∧ b = d := by
  have hab := cantor_interval a b
  have hcd := cantor_interval c d
  have hs : a+b = c+d := by
    by_cases hlt : a+b < c+d
    · have ht := triangular_mono (s := a+b+1) (t := c+d) (by omega)
      omega
    · by_cases hgt : c+d < a+b
      · have ht := triangular_mono (s := c+d+1) (t := a+b) (by omega)
        omega
      · omega
  unfold cantor at he
  rw [hs] at he
  omega

end C207Soundness
