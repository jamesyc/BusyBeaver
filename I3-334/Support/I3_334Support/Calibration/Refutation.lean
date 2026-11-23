module
public import I3_334Support.Calibration.InternalGraphSoundness
public import I3_334Support.Calibration.InternalTransport
public import I3_334Support.Calibration.InterpretationFacts
public import I3_334Support.Calibration.ArithmeticTheoryModels
public import Foundation.FirstOrder.Incompleteness.StandardProvability
@[expose] public section

namespace PalomarI3380.Calibration

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding CodedGraph

theorem model_distinction_excludes_refutation
    {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
    (D : OmegaDomain L inhabited)
    (distinct : (TermWords.stagedAlgebra (M := D.Points)).constant .D ≠
      TermWords.stagedAlgebra.constant .J) :
    ¬Bootstrapping.Provable arithmeticTheory (^⊥ : D.Points) := by
  obtain ⟨P,model⟩ := CodedGraph.Presentation.of_distinction D distinct
  obtain ⟨truth⟩ := CodedGraph.TruthTable.exists_table D P
  exact fun bad => truth.no_refutation D model (graph_refutation_of_arithmetic interpretation_facts bad)

theorem con_eval {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    arithmeticTheory.standardProvability.con.Evalb (![] : Fin 0 → M) ↔
       ¬Bootstrapping.Provable arithmeticTheory (^⊥ : M) := by
  simp [ProvabilityAbstraction.Provability.con,standardProvability_def,Function.comp_def,
    FFL.FirstOrder.Sentence.quote_falsum]

end PalomarI3380.Calibration
