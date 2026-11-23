module
public import I3_334Support.Calibration.FilterReading
public import I3_334Support.Equations.RecoveredI3
public import I3_334Support.Arithmetic.OmegaPeano
public import I3_334Support.Logic.Soundness
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Entailment
open SquareRepresentation

instance : 𝗘𝗤 FilterLanguage ⪯ filterTheory :=
  FFL.Entailment.WeakerThan.ofSubset fun _ => Or.inl

theorem source_model_of_filterTheory {A : Type} [Nonempty A]
    [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]
    (model : A↓[FilterLanguage] ⊧* filterTheory) :
    ∃ C : FilterModel A, Nonempty C.Domain ∧ Logic.ZFCI3Model C.mem := by
  have laws := equations_of_filter_model model
  obtain ⟨F,meaning,hit⟩ := ultrafilter_of_filter_model model
  let C : FilterModel A := ⟨laws,F,meaning⟩
  have separating := C.relationLaws.separates_of_filter laws F hit
  obtain ⟨N,same⟩ := C.square.namedModel_of_separated laws separating
  refine ⟨C,N.inhabited,?_⟩
  have membership : N.mem = C.mem := by
    funext x y
    change N.square.rel ((algebraOf A).constant .E) x y = _
    rw [same]
    rfl
  exact membership ▸ N.recovered_model

def interpretArithmetic (φ : ArithmeticSentence) : FFL.FirstOrder.Sentence FilterLanguage :=
  interpretSentence (Logic.readArithmetic φ)

theorem absorb_arithmetic {φ : ArithmeticSentence} (source : Logic.ZFCI3Provable (Logic.readArithmetic φ)) :
    filterTheory ⊢ interpretArithmetic φ := by
  apply Theory.Proof.complete
  apply consequence_iff_eq.mpr
  intro A _ _ _ model
  obtain ⟨C,⟨point⟩,sourceModel⟩ := source_model_of_filterTheory model
  let env := fun _ : Nat => point
  refine (interpretSentence_eval C _ (Logic.readArithmetic_closed φ) env).mpr ?_
  obtain ⟨Γ,axioms,proof⟩ := source
  exact Logic.NDSemantics.sound C.mem proof env (fun p hp => sourceModel p (axioms p hp) env)

end PalomarI3380.Calibration
