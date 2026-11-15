module
public import NumericCoding
@[expose] public section
namespace C209Soundness

theorem triangular_succ (s : Nat) :
    (s+1)*(s+1+1)/2 = s*(s+1)/2 + s+1 := by
  have he : (s+1)*(s+1+1) = s*(s+1) + 2*(s+1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  rw [he]
  omega

end C209Soundness
