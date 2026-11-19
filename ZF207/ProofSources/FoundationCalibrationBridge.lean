module
public import FoundationGateSemantics
public import FoundationBoundsBridge
public import FoundationSeparationBridge
public import FoundationBasicTheoryBridge
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def FoundationAxiomTranslation : Prop := ∀ p ∈ (𝗭𝗙 : SetTheory), SourceTheorem (axiomSource p)

/-- The only input here is translation of the actual Foundation ZF axioms.
The gate theorem itself is the checked model-theoretic/completeness result. -/
theorem positive_source_of_axiom_translation (hZF : FoundationAxiomTranslation)
 (a d h : Nat) (had : a≠d) (hah : a≠h) (hdh : d≠h) :
 SourceTheorem (positivePointedSource a d h) := by
 have ht := foundation_source_theorem (foundation_positive_proof a d h had hah hdh) hZF
 have hp := foundation_source_declose (ofSource 0 (positivePointedSource a d h)) ht
 obtain ⟨Γ,hΓ,hp⟩ := hp
 exact ⟨Γ,hΓ,ND.ie (toSource_ofSource_equiv _ 0 Γ).1 hp⟩

theorem reverse_of_foundation_axiom_translation (hZF : FoundationAxiomTranslation)
 (h : C207Soundness.ExactProvable 1) : ZfrProvable 0 :=
 reverse_calibration_pending_positive_witness (positive_source_of_axiom_translation hZF) h

/-- Exact remaining axiom family, isolated rather than silently assumed. -/
theorem foundation_axiom_translation_of_replacement
 (hR : ∀ p : SetTheorySemiproposition 2,
   SourceTheorem (axiomSource (Axiom.replacementSchema p))) : FoundationAxiomTranslation := by
 intro p hp
 rcases hp with (hb | hs) | hr
 · exact source_bst_axiom hb
 · cases hs with
   | separation q => exact source_separation_axiom q
 · cases hr with
   | replacement q => exact hR q

end ZFR.FoundationBridge
