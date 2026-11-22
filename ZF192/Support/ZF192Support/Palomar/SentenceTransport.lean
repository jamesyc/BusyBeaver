module
public import ZF192Support.Palomar.FoundationModels
public import ZF192Support.Logic.Foundation.Syntax.Bounds
@[expose] public section
namespace PalomarZF192Theory
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Canonical closed copied-source representative of an actual Foundation sentence. -/
def ofFoundationSentence (φ:SetTheorySentence):Formula :=
 ZFR.FoundationBridge.toSource (φ:Proposition Language.set)
theorem ofFoundationSentence_closed (φ:SetTheorySentence):Closed (ofFoundationSentence φ) := by
 simpa [Closed, ofFoundationSentence] using ZFR.FoundationBridge.toSource_bound_fvSup (φ:Proposition Language.set)
theorem ofFoundationSentence_eval {V:Type} [SetStructure V] [Nonempty V]
 (φ:SetTheorySentence)(s:Nat→V):
 eval (fun x y:V=>x∈y) (ofFoundationSentence φ) s ↔ V↓[Language.set] ⊧ φ := by
 rw [ofFoundationSentence]
 have hs:(fun i:Fin 0=>s i.val)=(![]:Fin 0→V):=Subsingleton.elim _ _
 simpa only [Semiformula.eval_emb,hs,models_iff,Semiformula.Realize,Semiformula.Evalb] using
  (ZFR.FoundationBridge.toSource_eval (φ:Proposition Language.set) s).symm
/-- Any proved uniform semantic identification transports provability both ways.
The meaning relation is a lemma input here, never an assumption in the final
Challenge theorem. No model existence or soundness premise is introduced. -/
theorem provable_iff_of_uniform (p:Formula)(φ:SetTheorySentence)
 (meaning:∀ (V:Type) [SetStructure V] [Nonempty V] [V↓[Language.set] ⊧* 𝗭𝗙],
   ∀ s:Nat→V,eval (fun x y:V=>x∈y) p s ↔ V↓[Language.set] ⊧ φ):
 Provable p ↔ (𝗭𝗙:SetTheory) ⊢ φ := by
 constructor
 · intro hp
   apply SetTheory.complete.{0}
   intro V _ _ _
   classical
   let s:Nat→V:=fun _=>Classical.choice (inferInstance:Nonempty V)
   have hs:=ZFR.NDSemantics.source_sound (fun x y:V=>x∈y)
    (ZFR.NDSemantics.all_source_zf_axioms_valid V) hp s
   exact (meaning V s).mp hs
 · intro hp
   apply ZFR.NDSemantics.foundation_proof_to_source
   apply SetTheory.complete.{0}
   intro V _ _ _
   rw [models_iff_proposition]
   intro s
   apply (ZFR.FoundationBridge.certificate_ofSource_eval p 0 ![] s).mpr
   exact (meaning V s).mpr (models_of_provable (inferInstance:V↓[Language.set] ⊧* 𝗭𝗙) hp)
theorem provable_ofFoundationSentence_iff (φ:SetTheorySentence):
 Provable (ofFoundationSentence φ) ↔ (𝗭𝗙:SetTheory) ⊢ φ :=
 provable_iff_of_uniform _ _ (fun _ _ _ _ s=>ofFoundationSentence_eval φ s)
theorem provable_neg_ofFoundationSentence_iff (φ:SetTheorySentence):
 Provable (Neg (ofFoundationSentence φ)) ↔ (𝗭𝗙:SetTheory) ⊢ ∼φ := by
 apply provable_iff_of_uniform
 intro V _ _ _ s
 simpa [Neg,eval] using
  not_congr (ofFoundationSentence_eval (V:=V) φ s)
end PalomarZF192Theory
