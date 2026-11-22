module
public import ZF192Support.Logic.Source.Derived.Negation
@[expose] public section
namespace ZFR

theorem nd_and_monotone {Γ : Context} {p p' q q' : Formula}
 (hp : ND (.seq Γ (.imp p p'))) (hq : ND (.seq Γ (.imp q q'))) :
 ND (.seq Γ (.imp (.and p q) (.and p' q'))) := by
 apply ND.ii
 have hc : ND (.seq (.and p q::Γ) (.and p q)) := ND.ctx (by simp)
 exact ND.ci (ND.ie hp.weaken_cons (ND.ce1 hc)) (ND.ie hq.weaken_cons (ND.ce2 hc))

theorem NDEquiv.and {Γ : Context} {p p' q q' : Formula}
 (hp : NDEquiv Γ p p') (hq : NDEquiv Γ q q') : NDEquiv Γ (.and p q) (.and p' q') :=
 ⟨nd_and_monotone hp.1 hq.1,nd_and_monotone hp.2 hq.2⟩

end ZFR
