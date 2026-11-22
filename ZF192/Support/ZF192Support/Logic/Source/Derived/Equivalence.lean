module
public import ZF192Support.Logic.Source.Derived.Congruence
@[expose] public section
namespace ZFR

def NDEquiv (Γ : Context) (p q : Formula) : Prop :=
 ND (.seq Γ (.imp p q)) ∧ ND (.seq Γ (.imp q p))

theorem NDEquiv.refl (Γ : Context) (p : Formula) : NDEquiv Γ p p :=
 ⟨ND.ii (ND.ctx (by simp)),ND.ii (ND.ctx (by simp))⟩

theorem NDEquiv.symm {Γ : Context} {p q : Formula} (h : NDEquiv Γ p q) : NDEquiv Γ q p :=
 ⟨h.2,h.1⟩

theorem NDEquiv.trans {Γ : Context} {p q r : Formula}
 (h : NDEquiv Γ p q) (k : NDEquiv Γ q r) : NDEquiv Γ p r := by
 constructor
 · exact ND.ii (ND.ie k.1.weaken_cons (ND.ie h.1.weaken_cons (ND.ctx (by simp))))
 · exact ND.ii (ND.ie h.2.weaken_cons (ND.ie k.2.weaken_cons (ND.ctx (by simp))))

theorem NDEquiv.imp {Γ : Context} {p p' q q' : Formula}
 (hp : NDEquiv Γ p p') (hq : NDEquiv Γ q q') : NDEquiv Γ (.imp p q) (.imp p' q') :=
 ⟨nd_imp_congruence hp.2 hq.1,nd_imp_congruence hp.1 hq.2⟩

theorem NDEquiv.all {Γ : Context} {p q : Formula}
 (h : NDEquiv (shiftContext Γ) p q) : NDEquiv Γ (.all p) (.all q) :=
 ⟨nd_all_monotone h.1,nd_all_monotone h.2⟩

theorem NDEquiv.ex {Γ : Context} {p q : Formula}
 (h : NDEquiv (shiftContext Γ) p q) : NDEquiv Γ (.ex p) (.ex q) :=
 ⟨nd_ex_monotone h.1,nd_ex_monotone h.2⟩

theorem NDEquiv.false_surrogate {Γ : Context} (i : Nat)
 (h : ND (.seq Γ (.imp (.mem i i) .bot))) : NDEquiv Γ (.mem i i) .bot :=
 ⟨h,ND.ii (ND.exp (ND.ctx (by simp)))⟩

end ZFR
