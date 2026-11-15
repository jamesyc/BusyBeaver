module
public import Halting.Calibration
public import Halting.Consistent
public import Independence.Top
@[expose] public section
/-! # The calibration of `T` and the compared claim

All four calibration premises hold for `T := theoryT tmpl`, with no further assumption. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF209.Independence ZF209.OmegaInterpretation

theorem calibration : Calibration (theoryT tmpl) literal209PhysicalSentence where
  base := base
  consistent := fun hZF => by have := hZF; exact consistent
  internal := internal tmpl interpFacts markAx_U
  absorb := fun _ h => absorb h

/-- The compared claim. -/
theorem exact209Claim : PalomarZF209.Exact209Claim :=
  exact209Claim_of_calibration calibration

end ZF209.Halting
