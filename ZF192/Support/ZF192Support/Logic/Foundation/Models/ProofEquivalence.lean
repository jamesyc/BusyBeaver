module
public import ZF192Support.Logic.Foundation.Models.ZF
public import ZF192Support.Logic.Foundation.Deduction.RoundTrip
public import ZF192Support.Logic.Foundation.Deduction.UniversalClosure
public import ZF192Support.Logic.Foundation.Axioms.ZF
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FoundationBridge
/-- External proof-existence calibration for EVERY source formula, not only
bottom. Universal closure is explicit, so open formulas are not hidden. -/
theorem source_proof_to_foundation {p : Formula}
 (hp : ZFR.SourceTheorem p) :
 (𝗭𝗙 : SetTheory) ⊢ (ofSource 0 p).univCl := by
 apply SetTheory.complete.{0}
 intro V _ _ _
 rw [models_iff_proposition]
 intro s
 apply (certificate_ofSource_eval p 0 ![] s).mpr
 exact source_sound (fun x y : V => x ∈ y) (all_source_zf_axioms_valid V) hp _

/-- Reverse external translation uses the already proved Foundation axiom
calibration, universal de-closure, and exact syntax round-trip equivalence. -/
theorem foundation_proof_to_source {p : Formula}
 (hp : (𝗭𝗙 : SetTheory) ⊢ (ofSource 0 p).univCl) :
 ZFR.SourceTheorem p := by
 have hs := foundation_source_theorem hp foundation_zf_axiom_translation
 obtain ⟨Γ,hΓ,hd⟩ := foundation_source_declose (ofSource 0 p) hs
 exact ⟨Γ,hΓ,ND.ie (toSource_ofSource_equiv p 0 Γ).1 hd⟩

end ZFR.NDSemantics
