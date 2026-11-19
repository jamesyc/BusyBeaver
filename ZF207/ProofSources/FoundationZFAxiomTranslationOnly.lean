module
public import FoundationTheoryBridge
public import FoundationBasicTheoryBridge
public import FoundationSeparationBridge
public import FoundationReplacementCertificate
public import Foundation.FirstOrder.SetTheory.ZF.Model
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Actual Foundation.ZF axiom translation, without importing unrelated
old gate/calibration or hierarchy-recursion developments. -/
theorem foundation_zf_axiom_translation :
 ∀ p ∈ (𝗭𝗙 : SetTheory), SourceTheorem (axiomSource p) := by
 intro p hp
 rcases hp with (hb | hs) | hr
 · exact source_bst_axiom hb
 · cases hs with
   | separation q => exact source_separation_axiom q
 · cases hr with
   | replacement q => exact source_replacement_axiom q
end ZFR.FoundationBridge
