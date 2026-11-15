module
public import FoundationCalibrationBridge
public import FoundationReplacementCertificate
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

theorem foundation_axiom_translation : FoundationAxiomTranslation :=
 foundation_axiom_translation_of_replacement source_replacement_axiom

/-- Unconditional extensional proof-existence calibration. This is not an
extracted executable or PA-internal proof-code compiler. -/
theorem exact_reverse_calibration (h : C209Soundness.ExactProvable 1) : ZfrProvable 0 :=
 reverse_of_foundation_axiom_translation foundation_axiom_translation h

end ZFR.FoundationBridge
