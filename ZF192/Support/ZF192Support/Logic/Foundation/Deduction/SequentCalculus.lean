module
public import ZF192Support.Logic.Foundation.Deduction.Negation
public import ZF192Support.Logic.Foundation.Syntax.Rewriting
public import Foundation.FirstOrder.LK.Basic
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder

/-- A refutation continuation over the actual Foundation multiset sequent. -/
def ExternalNeg (Γ : LK.Sequent Language.set) (Δ : Context) : Prop :=
 ∀ p, p ∈ Γ → ND (.seq Δ (.imp (toSource p) .bot))

def ExternalRefutes (Γ : LK.Sequent Language.set) : Prop :=
 ∀ Δ, ExternalNeg Γ Δ → ND (.seq Δ .bot)

theorem ExternalRefutes.extract {Γ : LK.Sequent Language.set}
 {p : Proposition Language.set} (h : ExternalRefutes (Γ + ⦃p⦄))
 {Δ : Context} (hn : ExternalNeg Γ Δ) : ND (.seq Δ (toSource p)) := by
 apply ND.ie (nd_double_negation Δ _)
 apply ND.ii
 apply h (.imp (toSource p) .bot :: Δ)
 intro q hq
 rcases Multiset.mem_add.mp hq with hg | hp
 · exact (hn q hg).weaken_cons
 · have he : q = p := by simpa using hp
   subst q; exact ND.ctx (by simp)

/-- Elimination of the actual pinned Foundation LK derivation into exact
source ND. This does not use model semantics or a mirrored calculus. -/
theorem external_derivation_refutes {Γ : LK.Sequent Language.set}
 (h : LK.Derivation Γ) : ExternalRefutes Γ := by
 induction h with
 | identity r v =>
   intro Δ hn
   have hp := hn (.rel r v) (by simp)
   have hn' := hn (.nrel r v) (by simp)
   exact ND.ie hn' hp
 | @cut Γ p Λ h1 h2 ih1 ih2 =>
   intro Δ hn
   have hp := ih1.extract (fun q hq => hn q (Multiset.mem_add.mpr (Or.inl hq)))
   have hnp := ih2.extract (fun q hq => hn q (Multiset.mem_add.mpr (Or.inr hq)))
   have hni := ND.ie (toSource_neg_equiv Δ p).1 hnp
   exact ND.ie hni hp
 | @contraction Γ p h ih =>
   intro Δ hn
   apply ih Δ
   intro q hq
   apply hn q
   simpa using hq
 | @weakening Γ p h ih =>
   intro Δ hn
   exact ih Δ (fun q hq => hn q (Multiset.mem_add.mpr (Or.inl hq)))
 | verum =>
   intro Δ hn
   exact ND.ie (hn .verum (by exact Multiset.mem_singleton.mpr rfl)) (nd_truth Δ)
 | @or Γ p q h ih =>
   intro Δ hn
   apply ih Δ
   intro r hr
   rcases Multiset.mem_add.mp hr with hg | hr
   · exact hn r (Multiset.mem_add.mpr (Or.inl hg))
   · simp only [Multiset.mem_add,Multiset.mem_singleton] at hr
     rcases hr with he | he
     · have he' : r = p := by simpa using he
       subst r
       apply ND.ii
       exact ND.ie (hn (.or p q) (by exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)))).weaken_cons (ND.di1 (ND.ctx (by simp)))
     · have he' : r = q := by simpa using he
       subst r
       apply ND.ii
       exact ND.ie (hn (.or p q) (by exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)))).weaken_cons (ND.di2 (ND.ctx (by simp)))
 | @and Γ p q h1 h2 ih1 ih2 =>
   intro Δ hn
   have hg : ExternalNeg Γ Δ := fun r hr => hn r (Multiset.mem_add.mpr (Or.inl hr))
   exact ND.ie (hn (.and p q) (by exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)))) (ND.ci (ih1.extract hg) (ih2.extract hg))
 | @all Γ p h ih =>
   intro Δ hn
   apply ND.ie (hn (.all p) (by exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))))
   apply ND.allI
   have hp := ih.extract (Δ := shiftContext Δ) (by
     intro r hr
     change r ∈ Γ.map Rewriting.shift at hr
     obtain ⟨q,hq,rfl⟩ := Multiset.mem_map.mp hr
     have ht := (hn q (Multiset.mem_add.mpr (Or.inl hq))).rename Nat.succ
     change ND (.seq (shiftContext Δ) (.imp (shift (toSource q)) .bot)) at ht
     rw [← toSource_shift q] at ht
     exact ht)
   change ND (.seq (shiftContext Δ) (toSource (Semiformula.rewAux Rew.free p))) at hp
   rw [toSource_free] at hp
   exact hp
 | @exs Γ p t h ih =>
   intro Δ hn
   apply ih Δ
   intro r hr
   rcases Multiset.mem_add.mp hr with hg | hr
   · exact hn r (Multiset.mem_add.mpr (Or.inl hg))
   · have he : r = p/[t] := by simpa using hr
     subst r
     change ND (.seq Δ (.imp (toSource (Semiformula.rewAux (Rew.subst ![t]) p)) .bot))
     rw [← Matrix.constant_eq_singleton,toSource_subst]
     apply ND.ii
     exact ND.ie (hn (.exs p) (by exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)))).weaken_cons (ND.exI (termIndex t) (ND.ctx (by simp)))

/-- A real Foundation finite theory proof becomes a source ND proof whenever
its individual translated premises have actual source ND derivations. -/
theorem external_theory_proof {S : LK.Sequent Language.set} {p : Proposition Language.set}
 (h : LK.Derivation (S.map Semiformula.neg + ⦃p⦄)) {Δ : Context}
 (hs : ∀ a, a ∈ S → ND (.seq Δ (toSource a))) : ND (.seq Δ (toSource p)) := by
 apply (external_derivation_refutes h).extract
 intro r hr
 obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hr
 apply ND.ii
 exact ND.ie (ND.ie (toSource_neg_equiv Δ a).1.weaken_cons (ND.ctx (by simp)))
   (hs a ha).weaken_cons

end ZFR.FoundationBridge
