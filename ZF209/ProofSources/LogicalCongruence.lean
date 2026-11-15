module
public import ClassicalEncoding
public import HeadTwoTemplate
@[expose] public section
namespace ZFR

theorem nd_imp_congruence {Γ : Context} {p p' q q' : Formula}
 (hp : ND (.seq Γ (.imp p' p))) (hq : ND (.seq Γ (.imp q q'))) :
 ND (.seq Γ (.imp (.imp p q) (.imp p' q'))) := by
 apply ND.ii
 apply ND.ii
 exact ND.ie hq.weaken_cons.weaken_cons
   (ND.ie (ND.ctx (by simp)) (ND.ie hp.weaken_cons.weaken_cons (ND.ctx (by simp))))

theorem nd_all_monotone {Γ : Context} {p q : Formula}
 (h : ND (.seq (shiftContext Γ) (.imp p q))) :
 ND (.seq Γ (.imp (.all p) (.all q))) := by
 apply ND.ii
 apply ND.allI
 have hp : ND (.seq (shiftContext (.all p::Γ)) p) := by
   have ht := ND.allE 0 (ND.ctx (Γ := shiftContext (.all p::Γ))
     (a := .all (rename (lift Nat.succ) p)) (by simp [shiftContext,shift,rename]))
   simpa only [subst_lift_shift] using ht
 exact ND.ie h.weaken_cons hp

theorem nd_ex_monotone {Γ : Context} {p q : Formula}
 (h : ND (.seq (shiftContext Γ) (.imp p q))) :
 ND (.seq Γ (.imp (.ex p) (.ex q))) := by
 apply ND.ii
 apply ND.exE (a := p)
 · exact ND.ctx (by simp)
 · change ND (.seq (p :: shiftContext (.ex p::Γ)) (.ex (rename (lift Nat.succ) q)))
   apply ND.exI 0
   rw [subst_lift_shift]
   exact ND.ie h.weaken_cons.weaken_cons (ND.ctx (by simp))

end ZFR
