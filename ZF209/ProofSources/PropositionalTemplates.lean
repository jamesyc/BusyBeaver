module
public import RuleTranslation
@[expose] public section
namespace ZFR
open C209Soundness

theorem nd_imp_code_intro {Γ : Context} (a b : Nat)
    (p : ND (.seq (translateCode id a :: Γ) (translateCode id b))) :
    ND (.seq Γ (translateCode id (4*cantor a b))) := by
  by_cases h : 4*cantor a b = 0
  · rw [h, translateCode_zero]; exact nd_truth Γ
  · rw [translateCode_imp_pos id a b h]; exact ND.ii p

/-- Exact rho8 numerical schema, with no side condition needed for this
propositional tautology. All nested zero-code aliases are handled. -/
theorem nd_rho8_code (Γ : Context) (a d h v : Nat) :
    ND (.seq Γ (translateCode id
      (4*cantor (4*cantor (4*cantor h v) d)
        (4*cantor (4*cantor d h) (4*cantor a h))))) := by
  apply nd_imp_code_intro
  apply nd_imp_code_intro
  apply nd_imp_code_intro
  apply ND.ie (ND.pc _ (translateCode id h) (translateCode id v))
  apply ND.ii
  apply nd_mp_code d h
  · apply nd_mp_code (4*cantor h v) d
    · apply nd_imp_code_intro
      apply ND.ie (a := translateCode id h)
      · exact ND.ctx (by simp)
      · exact ND.ctx (by simp)
    · exact ND.ctx (by simp)
  · exact ND.ctx (by simp)

end ZFR
