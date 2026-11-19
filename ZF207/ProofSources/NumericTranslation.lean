module
public import NamedTranslation
public import ComputableDecoding
public import CantorUniqueness
@[expose] public section
namespace ZFR
open C207Soundness

theorem unpair_cantor (a b : Nat) : unpair (cantor a b) = (a,b) := by
  have h := cantor_injective (unpair_spec (cantor a b))
  exact Prod.ext h.1 h.2

theorem decode_allCode (a i : Nat) :
    decodeNat (4 * cantor a i + 2) = .all i (decodeNat a) := by
  rw [decodeNat]
  have hn : 4 * cantor a i + 2 ≠ 0 := by omega
  simp only [hn, dite_false]
  have hq : (4 * cantor a i + 2) / 4 = cantor a i := by omega
  have ht : (4 * cantor a i + 2) % 4 = 2 := by omega
  simp [hq, ht, unpair_cantor]

theorem decode_impCode_pos (a b : Nat) (h : 4 * cantor a b ≠ 0) :
    decodeNat (4 * cantor a b) = .imp (decodeNat a) (decodeNat b) := by
  rw [decodeNat]
  simp only [h, dite_false]
  have hq : (4 * cantor a b) / 4 = cantor a b := by omega
  have ht : (4 * cantor a b) % 4 = 0 := by omega
  simp [hq, ht, unpair_cantor]

def translateCode (ρ : Nat → Nat) (n : Nat) : ZFR.Formula :=
  translate ρ (decodeNat n)

theorem translateCode_all (ρ : Nat → Nat) (a i : Nat) :
    translateCode ρ (4*cantor a i+2) =
      ZFR.Formula.all (translateCode (bindName i ρ) a) := by
  simp [translateCode, decode_allCode, translate]

theorem translateCode_imp_pos (ρ : Nat → Nat) (a b : Nat) (h : 4*cantor a b≠0) :
    translateCode ρ (4*cantor a b) =
      ZFR.Formula.imp (translateCode ρ a) (translateCode ρ b) := by
  simp [translateCode, decode_impCode_pos a b h, translate]

theorem translateCode_zero (ρ : Nat → Nat) :
    translateCode ρ 0 = ZFR.Formula.imp .bot .bot := by
  simp [translateCode, decodeNat, translate]

theorem translateCode_gen (i n : Nat) :
    translateCode id (4*cantor n i+2) =
      ZFR.Formula.all (rename (generalizeMap i) (translateCode id n)) := by
  rw [translateCode_all]
  congr 1
  exact (generalize_translation i (decodeNat n)).symm

end ZFR
