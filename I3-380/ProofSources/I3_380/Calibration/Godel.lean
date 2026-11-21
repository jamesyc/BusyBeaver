module
public import I3_380.Arithmetic.OmegaReading
public import I3_380.Logic.Completeness
public import I3_380.Logic.Halting
public import Foundation.FirstOrder.Incompleteness.StandardProvability
@[expose] public section

namespace PalomarI3380.Logic

open Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- A recursive arithmetic theory calibrated to the literal nonhalting
sentence and to the arithmetic consequences of the source theory. -/
structure ArithmeticCalibration (A : ArithmeticTheory) [A.Δ₁] : Prop where
  extendsSigmaOne : 𝗜𝚺₁ ⪯ A
  consistent : ZFCI3Consistent → FFL.Entailment.Consistent A
  internalConsistency : ZFCI3Provable
    (.imp (Neg haltingSentence) (readArithmetic A.standardProvability.con))
  absorb : ∀ φ : ArithmeticSentence, ZFCI3Provable (readArithmetic φ) → A ⊢ φ

theorem ArithmeticCalibration.nonhalting_unprovable {A : ArithmeticTheory} [A.Δ₁]
    (calibration : ArithmeticCalibration A) (consistency : ZFCI3Consistent) :
    ¬ZFCI3Provable (Neg haltingSentence) := by
  letI : 𝗜𝚺₁ ⪯ A := calibration.extendsSigmaOne
  letI : FFL.Entailment.Consistent A := calibration.consistent consistency
  intro refutation
  have h : Theory.Derives ZFCI3Axiom
      (.imp (Neg haltingSentence) (readArithmetic A.standardProvability.con)) := calibration.internalConsistency
  exact ProvabilityAbstraction.con_unprovable (𝔅 := A.standardProvability)
    (calibration.absorb _ (h.app refutation))

end PalomarI3380.Logic
