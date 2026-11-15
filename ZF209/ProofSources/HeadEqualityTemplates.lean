module
public import EqualityTemplates
public import AtomicTranslation
@[expose] public section
namespace ZFR
open C209Soundness

theorem nd_head3_code {Γ : Context} (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ)
    (a d h : Nat) : ND (.seq Γ (translateCode id
      (4*cantor (4*cantor h d+3) (4*cantor (4*cantor a h+1) (4*cantor a d+1))))) := by
  have hp : 4*cantor (4*cantor a h+1) (4*cantor a d+1) ≠ 0 := by
    have := cantor_ge_right (4*cantor a h+1) (4*cantor a d+1); omega
  have hq : 4*cantor (4*cantor h d+3) (4*cantor (4*cantor a h+1) (4*cantor a d+1)) ≠ 0 := by
    have := cantor_ge_left (4*cantor h d+3) (4*cantor (4*cantor a h+1) (4*cantor a d+1)); omega
  rw [translateCode_imp_pos _ _ _ hq, translateCode_imp_pos _ _ _ hp]
  simp only [translateCode_eq, translateCode_mem, id_eq]
  exact nd_mem_container_eq hr he a h d

theorem nd_head4_code {Γ : Context} (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ)
    (a d h : Nat) : ND (.seq Γ (translateCode id
      (4*cantor (4*cantor h d+1) (4*cantor (4*cantor h a+3) (4*cantor a d+1))))) := by
  have hp : 4*cantor (4*cantor h a+3) (4*cantor a d+1) ≠ 0 := by
    have := cantor_ge_right (4*cantor h a+3) (4*cantor a d+1); omega
  have hq : 4*cantor (4*cantor h d+1) (4*cantor (4*cantor h a+3) (4*cantor a d+1)) ≠ 0 := by
    have := cantor_ge_left (4*cantor h d+1) (4*cantor (4*cantor h a+3) (4*cantor a d+1)); omega
  rw [translateCode_imp_pos _ _ _ hq, translateCode_imp_pos _ _ _ hp]
  simp only [translateCode_eq, translateCode_mem, id_eq]
  exact nd_mem_element_eq hr he h d a

end ZFR
