module
public import ConcreteChallengeSemantics
@[expose] public section
/-! Checked Foundation bridge, with no added consistency or soundness assumption. -/
namespace PalomarZF209
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- The copied source axioms also suffice for every actual Foundation ZF axiom. -/
theorem challenge_model_to_foundation {V:Type} [SetStructure V] [Nonempty V]
 (h:Model (fun x y:V=>x∈y)) : V↓[Language.set] ⊧* 𝗭𝗙 := by
 classical
 apply models_theory_iff.mpr
 intro φ hφ
 have ht:=ZFR.FoundationBridge.foundation_zf_axiom_translation φ hφ
 let s:Nat→V:=fun _=>Classical.choice (inferInstance:Nonempty V)
 have he:=ZFR.NDSemantics.source_sound (fun x y:V=>x∈y)
  ((model_iff_source _).mp h) ht s
 have hf:=(ZFR.FoundationBridge.toSource_eval (φ:Proposition Language.set) s).mpr he
 have hs:(fun i:Fin 0=>s i.val)=(![]:Fin 0→V):=Subsingleton.elim _ _
 simpa only [Semiformula.eval_emb,hs,models_iff,Semiformula.Realize,Semiformula.Evalb] using hf

theorem consistent_iff_foundation :
 Consistent ↔ FFL.Entailment.Consistent (𝗭𝗙:SetTheory) := by
 have hb : (ZFR.FoundationBridge.ofSource 0 (toSource .bot)).univCl=(⊥:SetTheorySentence) := by
  change ((⊥:SetTheorySentence):Proposition Language.set).univCl=⊥
  exact Semiformula.univCl_coe_sentence _
 rw [Consistent,provable_iff,FFL.Entailment.consistent_iff_unprovable_bot]
 constructor
 · intro hc hp
   apply hc
   apply ZFR.NDSemantics.foundation_proof_to_source
   simpa only [hb] using hp
 · intro hc hp
   apply hc
   simpa only [hb] using
    ZFR.NDSemantics.source_proof_to_foundation hp
end PalomarZF209
