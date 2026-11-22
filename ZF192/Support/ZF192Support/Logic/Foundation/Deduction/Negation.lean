module
public import ZF192Support.Logic.Foundation.Syntax.ToSource
public import ZF192Support.Logic.Source.Derived.Conjunction
@[expose] public section
namespace ZFR.FoundationBridge
open FFL.FirstOrder

/-- All helpers are derivations in the actual source ND, not semantic lemmas. -/
theorem nd_or_monotone {Γ : Context} {p p' q q' : ZFR.Formula}
 (hp : ND (.seq Γ (.imp p p'))) (hq : ND (.seq Γ (.imp q q'))) :
 ND (.seq Γ (.imp (.or p q) (.or p' q'))) := by
 apply ND.ii
 apply ND.de (a := p) (b := q) (ND.ctx (by simp))
 apply ND.branchPair
 · exact ND.di1 (ND.ie hp.weaken_cons.weaken_cons (ND.ctx (by simp)))
 · exact ND.di2 (ND.ie hq.weaken_cons.weaken_cons (ND.ctx (by simp)))

theorem or_equiv {Γ : Context} {p p' q q' : ZFR.Formula}
 (hp : NDEquiv Γ p p') (hq : NDEquiv Γ q q') : NDEquiv Γ (.or p q) (.or p' q') :=
 ⟨nd_or_monotone hp.1 hq.1,nd_or_monotone hp.2 hq.2⟩

theorem double_neg_equiv (Γ : Context) (p : ZFR.Formula) :
 NDEquiv Γ (.imp (.imp p .bot) .bot) p := by
 constructor
 · exact nd_double_negation Γ p
 · apply ND.ii; apply ND.ii
   exact ND.ie (a := p) (ND.ctx (by simp)) (ND.ctx (by simp))

theorem neg_and_equiv (Γ : Context) (p q : ZFR.Formula) :
 NDEquiv Γ (.or (.imp p .bot) (.imp q .bot)) (.imp (.and p q) .bot) := by
 constructor
 · apply ND.ii; apply ND.ii
   apply ND.de (a := .imp p .bot) (b := .imp q .bot) (ND.ctx (by simp))
   apply ND.branchPair
   · exact ND.ie (a := p) (ND.ctx (by simp)) (ND.ce1 (b := q) (ND.ctx (by simp)))
   · exact ND.ie (a := q) (ND.ctx (by simp)) (ND.ce2 (a := p) (ND.ctx (by simp)))
 · apply ND.ii
   apply ND.ie (ND.pc _ (.or (.imp p .bot) (.imp q .bot)) .bot)
   apply ND.ii
   apply ND.exp
   apply ND.ie (a := .and p q) (ND.ctx (by simp))
   apply ND.ci
   · apply ND.ie (nd_double_negation _ p)
     apply ND.ii
     exact ND.ie (a := .or (.imp p .bot) (.imp q .bot)) (ND.ctx (by simp)) (ND.di1 (ND.ctx (by simp)))
   · apply ND.ie (nd_double_negation _ q)
     apply ND.ii
     exact ND.ie (a := .or (.imp p .bot) (.imp q .bot)) (ND.ctx (by simp)) (ND.di2 (ND.ctx (by simp)))

theorem neg_or_equiv (Γ : Context) (p q : ZFR.Formula) :
 NDEquiv Γ (.and (.imp p .bot) (.imp q .bot)) (.imp (.or p q) .bot) := by
 constructor
 · apply ND.ii; apply ND.ii
   apply ND.de (a := p) (b := q) (ND.ctx (by simp))
   apply ND.branchPair
   · exact ND.ie (a := p) (ND.ce1 (b := .imp q .bot) (ND.ctx (by simp))) (ND.ctx (by simp))
   · exact ND.ie (a := q) (ND.ce2 (a := .imp p .bot) (ND.ctx (by simp))) (ND.ctx (by simp))
 · apply ND.ii
   apply ND.ci
   · apply ND.ii
     exact ND.ie (a := .or p q) (ND.ctx (by simp)) (ND.di1 (ND.ctx (by simp)))
   · apply ND.ii
     exact ND.ie (a := .or p q) (ND.ctx (by simp)) (ND.di2 (ND.ctx (by simp)))

theorem neg_all_equiv (Γ : Context) (p : ZFR.Formula) :
 NDEquiv Γ (.ex (.imp p .bot)) (.imp (.all p) .bot) :=
 (NDEquiv.ex_encoding Γ (.imp p .bot)).trans
   ((NDEquiv.all (double_neg_equiv (shiftContext Γ) p)).imp (NDEquiv.refl Γ .bot))

theorem neg_ex_equiv (Γ : Context) (p : ZFR.Formula) :
 NDEquiv Γ (.all (.imp p .bot)) (.imp (.ex p) .bot) :=
 (((NDEquiv.ex_encoding Γ p).imp (NDEquiv.refl Γ .bot)).trans
   (double_neg_equiv Γ (.all (.imp p .bot)))).symm

theorem neg_truth_equiv (Γ : Context) :
 NDEquiv Γ .bot (.imp (.imp .bot .bot) .bot) := by
 constructor
 · apply ND.ii; exact ND.exp (ND.ctx (by simp))
 · apply ND.ii
   exact ND.ie (ND.ctx (by simp)) (nd_truth _)

/-- Foundation's actual NNF negation translates to source implication-to-bot.
The recursion is on the real pinned Semiformula type, with quantifier cases
proved by source ND eigenvariable and existential rules. -/
theorem toSource_neg_equiv (Γ : Context) {n : Nat}
 (p : Semiformula Language.set Nat n) :
 NDEquiv Γ (toSource (Semiformula.neg p)) (.imp (toSource p) .bot) := by
 induction p generalizing Γ with
 | verum => exact neg_truth_equiv Γ
 | falsum => exact NDEquiv.refl Γ _
 | rel r v => exact NDEquiv.refl Γ _
 | nrel r v => exact (double_neg_equiv Γ (atom r v)).symm
 | and p q ihp ihq =>
   exact (or_equiv (ihp Γ) (ihq Γ)).trans (neg_and_equiv Γ _ _)
 | or p q ihp ihq =>
   exact ((ihp Γ).and (ihq Γ)).trans (neg_or_equiv Γ _ _)
 | all p ih =>
   exact (NDEquiv.ex (ih (shiftContext Γ))).trans (neg_all_equiv Γ _)
 | exs p ih =>
   exact (NDEquiv.all (ih (shiftContext Γ))).trans (neg_ex_equiv Γ _)


/-- Foundation's implication is NNF disjunction, not the source implication
constructor. This is the actual proof-level connection needed by imported axioms. -/
theorem arrow_equiv (Γ : Context) (p q : ZFR.Formula) :
 NDEquiv Γ (.or (.imp p .bot) q) (.imp p q) := by
 constructor
 · apply ND.ii; apply ND.ii
   apply ND.de (a := .imp p .bot) (b := q) (ND.ctx (by simp))
   apply ND.branchPair
   · apply ND.exp
     exact ND.ie (a := p) (ND.ctx (by simp)) (ND.ctx (by simp))
   · exact ND.ctx (by simp)
 · apply ND.ii
   apply ND.ie (ND.pc _ (.or (.imp p .bot) q) .bot)
   apply ND.ii
   apply ND.exp
   apply ND.ie (a := .or (.imp p .bot) q) (ND.ctx (by simp))
   apply ND.di2
   apply ND.ie (a := p) (ND.ctx (by simp))
   apply ND.ie (nd_double_negation _ p)
   apply ND.ii
   exact ND.ie (a := .or (.imp p .bot) q) (ND.ctx (by simp)) (ND.di1 (ND.ctx (by simp)))

theorem toSource_arrow_equiv (Γ : Context) {n : Nat}
 (p q : Semiformula Language.set Nat n) :
 NDEquiv Γ (toSource (.or (Semiformula.neg p) q)) (.imp (toSource p) (toSource q)) :=
 (or_equiv (toSource_neg_equiv Γ p) (NDEquiv.refl Γ _)).trans (arrow_equiv Γ _ _)

end ZFR.FoundationBridge
