module
public import NumericTranslation
@[expose] public section
namespace ZFR
open C209Soundness

theorem translateCode_mem (ρ : Nat → Nat) (a b : Nat) :
    translateCode ρ (4*cantor a b+1) = .mem (ρ a) (ρ b) := by
  unfold translateCode
  rw [decodeNat]
  have hn : 4*cantor a b+1 ≠ 0 := by omega
  have hq : (4*cantor a b+1)/4 = cantor a b := by omega
  have ht : (4*cantor a b+1)%4 = 1 := by omega
  simp [hn,hq,ht,unpair_cantor,translate]

theorem translateCode_eq (ρ : Nat → Nat) (a b : Nat) :
    translateCode ρ (4*cantor a b+3) = .eq (ρ a) (ρ b) := by
  unfold translateCode
  rw [decodeNat]
  have hn : 4*cantor a b+3 ≠ 0 := by omega
  have hq : (4*cantor a b+3)/4 = cantor a b := by omega
  have ht : (4*cantor a b+3)%4 = 3 := by omega
  simp [hn,hq,ht,unpair_cantor,translate]
end ZFR
