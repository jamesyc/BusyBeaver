module
public import GeneralizationBridge
@[expose] public section
namespace ZFR
open C209Soundness

theorem nd_truth (Γ : Context) : ND (.seq Γ (.imp .bot .bot)) :=
  ND.ii (ND.ctx (by simp))

/-- Exact C-MP translation, including the numerical collision Imp(0,0)=0. -/
theorem nd_mp_code {Γ : Context} (a b : Nat)
    (pa : ND (.seq Γ (translateCode id a)))
    (pab : ND (.seq Γ (translateCode id (4*cantor a b)))) :
    ND (.seq Γ (translateCode id b)) := by
  by_cases h : 4*cantor a b = 0
  · have hb := cantor_ge_right a b
    have bz : b = 0 := by omega
    rw [bz, translateCode_zero]
    exact nd_truth Γ
  · rw [translateCode_imp_pos id a b h] at pab
    exact ND.ie pab pa

end ZFR
