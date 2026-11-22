module
public import ZF192.Proof.Calibration
public import ZF192.Palomar.Representation
public import ZF192.Proof.SigmaSoundness
public import ZF192Support.Palomar.SigmaSoundness
public import ZF192Support.Independence.Theory.Consistency

@[expose] public section
namespace ZF192

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF192Support.OmegaInterpretation ZF192Support.Independence

/-- The compared claim, given a calibrated arithmetic theory. -/
theorem exact192Claim_of_calibration {T : ArithmeticTheory} [T.Δ₁]
    (hT : Calibration T literal192PhysicalSentence) : PalomarZF192.Exact192Claim := by
  have sigma : PalomarZF192Theory.ArithmeticSigma1Sound → ArithmeticSigma1SoundZF :=
    SigmaBridge.standalone_sound_implies_production
  refine ⟨haltSentence, haltSentence_represents, fun hc hp => ?_, fun hs => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have := PalomarZF192Theory.consistent_iff_foundation.mp hc
    exact neg_unprovable_of_calibration hT
      ((PalomarZF192Theory.provable_neg_ofFoundationSentence_iff literal192PhysicalSentence).mp hp)
  · exact literal192_physical_unprovable (sigma hs)
      ((PalomarZF192Theory.provable_ofFoundationSentence_iff literal192PhysicalSentence).mp hp)
  · have := (sigma hs).consistent
    exact neg_unprovable_of_calibration hT
      ((PalomarZF192Theory.provable_neg_ofFoundationSentence_iff literal192PhysicalSentence).mp hp)


theorem calibration :
    Calibration (ZF192Support.Halting.theoryT ZF192Support.Halting.tmpl) literal192PhysicalSentence where
  base := ZF192Support.Halting.base
  consistent := fun hZF => by have := hZF; exact ZF192Support.Halting.consistent
  internal := ZF192.internal ZF192Support.Halting.tmpl ZF192Support.Halting.interpFacts ZF192Support.Halting.markAx_U
  absorb := fun _ h => ZF192Support.Halting.absorb h

end ZF192

namespace PalomarZF192

theorem exact192Claim : Exact192Claim := ZF192.exact192Claim_of_calibration ZF192.calibration

theorem nonhalting_of_consistent (h : PalomarZF192Theory.Consistent) :
    ¬ BinaryTape.Halts machine (BinaryTape.zc 0 [] []) := by
  have table_eq : PalomarZF192History.literalRows = M192.literalRows := rfl
  have machine_eq : machine = M192.literal := by
    unfold machine M192.literal M192.tmOf
    rw [table_eq]
  rw [machine_eq]
  letI := PalomarZF192Theory.consistent_iff_foundation.mp h
  exact ZF192.literal192_nonhalting_of_foundation_consistent

end PalomarZF192
