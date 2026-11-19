module
public import QuantifierTemplates
@[expose] public section
namespace ZFR
open C207Soundness

/-- The exact numerical first C axiom family, directly derived in source ND. -/
theorem nd_head1_code (Γ : Context) (a d h : Nat) :
    ND (.seq Γ (translateCode id
      (4*cantor (4*cantor a d+2)
        (4*cantor (4*cantor (4*cantor a h) d+2) (4*cantor h d+2))))) := by
  by_cases hi : 4*cantor a h = 0
  · have hh := cantor_ge_right a h
    have hz : h = 0 := by omega
    apply nd_imp_code_intro
    apply nd_imp_code_intro
    simp only [hz, translateCode_all, translateCode_zero]
    exact ND.allI (nd_truth _)
  · have hp : 4*cantor (4*cantor (4*cantor a h) d+2) (4*cantor h d+2) ≠ 0 := by
      have := cantor_ge_right (4*cantor (4*cantor a h) d+2) (4*cantor h d+2)
      omega
    have hq : 4*cantor (4*cantor a d+2)
        (4*cantor (4*cantor (4*cantor a h) d+2) (4*cantor h d+2)) ≠ 0 := by
      have := cantor_ge_left (4*cantor a d+2)
        (4*cantor (4*cantor (4*cantor a h) d+2) (4*cantor h d+2))
      omega
    rw [translateCode_imp_pos _ _ _ hq, translateCode_imp_pos _ _ _ hp]
    simp only [translateCode_all, translateCode_imp_pos _ _ _ hi]
    exact nd_all_distribution Γ _ _

end ZFR
