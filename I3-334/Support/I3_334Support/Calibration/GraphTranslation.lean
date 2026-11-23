module
public import I3_334Support.Calibration.ArithmeticTemplates
public import I3_334Support.Calibration.CraigPadding
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticInterpretation

theorem kax_closed {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (ι : Interp) {s : M} (formula : IsFormula ℒₒᵣ s) (fixed : shift ℒₒᵣ s = s) :
    shift GraphLanguage (kax ι s) = kax ι s := by
  have mark : IsSemiformula GraphLanguage 1 (markAt ι (^#0 : M)) := markAt_semiformula ι (by simp)
  have translated := jhat_semiformula ι formula
  have wider : IsSemiformula ℒₒᵣ 1 s := ⟨formula.isUFormula,le_trans formula.bv_le (by simp)⟩
  have lhs : shift GraphLanguage (jhat ι s) = jhat ι s := by
    have shifted := J_shift ι 1 s wider (^#0) (by simp)
    simpa [jhat,fixed] using shifted.symm
  have rhs : shift GraphLanguage (markAt ι (^#0 : M)) = markAt ι (^#0 : M) := by
    rw [shift_markAt ι (show IsSemiterm GraphLanguage 1 (^#0 : M) by simp)]
    simp
  simp [kax,imp,mark.isUFormula,translated.isUFormula,shift_neg mark,rhs,lhs]

theorem translation_closed (φ : ArithmeticSentence) :
    shift GraphLanguage (⌜kaxP filterInterpretation φ⌝ : Nat) = ⌜kaxP filterInterpretation φ⌝ := by
  rw [quote_kaxP]
  exact kax_closed filterInterpretation (Sentence.quote_isSemiformula₀ φ) (Sentence.shift_quote φ)

noncomputable def translatedSentence (φ : ArithmeticSentence) : FFL.FirstOrder.Sentence GraphLanguage :=
  Classical.choose (Craig.sentence_of_closedCode (kaxP filterInterpretation φ) (translation_closed φ))

theorem translatedSentence_spec (φ : ArithmeticSentence) :
    kaxP filterInterpretation φ = Rewriting.emb (translatedSentence φ) :=
  Classical.choose_spec (Craig.sentence_of_closedCode (kaxP filterInterpretation φ) (translation_closed φ))

theorem translatedSentence_quote (φ : ArithmeticSentence) :
    (⌜translatedSentence φ⌝ : Nat) = kax filterInterpretation (⌜φ⌝ : Nat) := by
  rw [Sentence.quote_def,← translatedSentence_spec,quote_kaxP]

noncomputable def translationGraph : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out source. ∃ b m j i, !qqBvarDef b 0 ∧ !(markAtDef filterInterpretation) m b ∧
    !(JDef filterInterpretation) j b 1 source ∧ !(impGraph GraphLanguage) i m j ∧ !qqAllDef out i”

theorem translation_defined {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺ᴬ₁-Function₁ (kax (V := M) filterInterpretation) via translationGraph :=
  .mk fun v => by
    simp [translationGraph,kax,jhat,(markAt_defined filterInterpretation).iff,
      (J_defined filterInterpretation).iff,imp.defined.iff]

end PalomarI3380.Calibration
