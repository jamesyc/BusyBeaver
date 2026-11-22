module
public import ZF192Support.Logic.Source.Deduction
@[expose] public section
namespace ZFR

/-- Exact zfcRefl and zfcEqElem from zfc_fixed.mm0, not added ND rules. -/
def zfrRefl : Formula := .all (.eq 0 0)
def zfrEqElem : Formula := .all (.all (.all (.all
  (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0)))))))

theorem nd_refl_instance {Γ : Context} (h : zfrRefl ∈ Γ) (a : Nat) :
    ND (.seq Γ (.eq a a)) := by
  exact ND.allE a (ND.ctx h)

theorem nd_eqElem_instance {Γ : Context} (h : zfrEqElem ∈ Γ) (a b c d : Nat) :
    ND (.seq Γ (.imp (.eq a c) (.imp (.eq b d) (.imp (.mem a b) (.mem c d))))) := by
  have ht := ND.allE d (ND.allE c (ND.allE b (ND.allE a (ND.ctx h))))
  simpa [zfrEqElem, subst, rename, lift, substMap] using ht

theorem nd_mem_container_eq {Γ : Context}
    (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ) (a h d : Nat) :
    ND (.seq Γ (.imp (.eq h d) (.imp (.mem a h) (.mem a d)))) := by
  have ht := nd_eqElem_instance he a h a d
  exact ND.ie ht (nd_refl_instance hr a)

theorem nd_mem_element_eq {Γ : Context}
    (hr : zfrRefl ∈ Γ) (he : zfrEqElem ∈ Γ) (h d a : Nat) :
    ND (.seq Γ (.imp (.mem h d) (.imp (.eq h a) (.mem a d)))) := by
  apply ND.ii
  apply ND.ii
  have ht := nd_eqElem_instance (Γ := .eq h a :: .mem h d :: Γ)
    (by simp [he]) h d a d
  exact ND.ie (ND.ie (ND.ie ht (ND.ctx (by simp)))
    (nd_refl_instance (by simp [hr]) d)) (ND.ctx (by simp))

end ZFR
