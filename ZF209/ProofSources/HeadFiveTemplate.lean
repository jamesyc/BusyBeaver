module
public import QuantifierCommutation
@[expose] public section
namespace ZFR
open C209Soundness

theorem swap_named_binders (a d : Nat) (had : a ≠ d) (p : C209Soundness.Formula) :
    rename swap01 (translate (bindName a (bindName d id)) p) =
    translate (bindName d (bindName a id)) p := by
  rw [rename_translate]
  congr 1
  funext j
  by_cases ha : j = a
  · subst j; simp [bindName, had, swap01]
  · by_cases hd : j = d
    · subst j; simp [bindName, ha, swap01]
    · simp [bindName, ha, hd, swap01]

theorem nd_head5_code (Γ : Context) (a d h : Nat) :
    ND (.seq Γ (translateCode id
      (4*cantor (4*cantor (4*cantor h a+2) d+2)
        (4*cantor (4*cantor h d+2) a+2)))) := by
  by_cases had : a = d
  · subst a
    apply nd_imp_code_intro
    exact ND.ctx (by simp)
  · have hp : 4*cantor (4*cantor (4*cantor h a+2) d+2)
        (4*cantor (4*cantor h d+2) a+2) ≠ 0 := by
      have := cantor_ge_right (4*cantor (4*cantor h a+2) d+2)
        (4*cantor (4*cantor h d+2) a+2)
      omega
    rw [translateCode_imp_pos _ _ _ hp]
    simp only [translateCode_all]
    have ht := nd_all_commute Γ (translate (bindName a (bindName d id)) (decodeNat h))
    rw [swap_named_binders a d had] at ht
    exact ht

end ZFR
