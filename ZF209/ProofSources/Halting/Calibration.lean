module
public import Halting.Premise
public import ConcreteArithmeticProofTransport
public import Literal209SigmaSoundness
public import Independence.Godel
@[expose] public section
/-! # Calibration premises for `T ι`

`internal`: in every model of PA, `¬Con_T` is an internal `T`-refutation, which halts the
literal machine (`internal_halts`); completeness gives `PA ⊢ ¬halt → Con_T`, and the ω-reading
moves it to ZF. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF209.OmegaInterpretation ZF209.Internal.Arith

theorem pa_not_halt_con (ι : Interp) (hF : InterpFacts ι theoryU) (hMk : theoryU ⊢ markAx ι) :
    𝗣𝗔 ⊢ ∼BinaryTape.physicalHaltSentence 🡒 (Theory.standardProvability (theoryT ι)).con := by
  apply Arithmetic.complete.{0}
  intro V _ _
  have hh := BinaryTape.physicalHaltSentence_eval (M := V)
  simp only [models_iff] at hh ⊢
  simp [hh]
  intro hn
  simp only [ProvabilityAbstraction.Provability.con, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq]
  intro hp
  have hp' := by simpa [models_iff, FFL.FirstOrder.Arithmetic.standardProvability_def] using hp
  exact hn (internal_halts ι hF hMk hp')

theorem internal (ι : Interp) (hF : InterpFacts ι theoryU) (hMk : theoryU ⊢ markAx ι) :
    (𝗭𝗙 : SetTheory) ⊢ ∼literal209PhysicalSentence 🡒
      arithmeticTranslation.translate (Theory.standardProvability (theoryT ι)).con := by
  simpa [literal209PhysicalSentence] using pa_proof_to_zf (pa_not_halt_con ι hF hMk)

end ZF209.Halting
