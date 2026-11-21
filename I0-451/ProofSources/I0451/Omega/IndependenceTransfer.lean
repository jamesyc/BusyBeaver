module
public import I0451.Sentence
public import I0451.Omega.ConsistencyTransfer
public import I0451.ArithmeticNativeSentence

/-! The incompleteness argument with its proof-code and large-cardinal
inputs explicit. These lemmas use the same omega interpretation for
the consistency sentence and the literal halting sentence. -/
@[expose] public section
namespace I0451

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Omega ZF207.OmegaInterpretation

theorem ArithmeticSigmaOneSound.consistent {T : SetTheory} [𝗭𝗙 ⪯ T]
    (sound : ArithmeticSigmaOneSound T) : Entailment.Consistent T := by
  apply Entailment.consistent_iff_unprovable_bot.mpr
  intro refutation
  let falseSentence : 𝚺ᴬ₁.Sentence := .mkSigma “⊥”
  have falseProof : T ⊢ arithmeticTranslation.translate falseSentence.val := by
    exact Entailment.efq ⨀ refutation
  have impossible := sound falseSentence falseProof
  simp [falseSentence] at impossible

set_option maxHeartbeats 1000000 in
/-- The literal machine's proof-code calibration converts nonhalting
to consistency of the searched theory in arithmetic. An internal proof
of the target's consistency then gives the Gödel II obstruction. -/
theorem nonhalting_unprovable_of_calibration (B T : SetTheory) [𝗭𝗙 ⪯ B] [𝗭𝗙 ⪯ T]
    [(arithmeticConsequences B).RE] [(arithmeticConsequences T).RE]
    (consistent : Entailment.Consistent T)
    (calibration : 𝗣𝗔 ⊢ (∼arithmeticHalting.val) 🡒 (arithmeticConsequences B).craig.consistent.val)
    (relative :
      B ⊢ arithmeticTranslation.translate (arithmeticConsequences T).craig.standardProvability.con) :
    T ⊬ ∼setHalting := by
  let searched := (arithmeticConsequences B).craig
  let target := (arithmeticConsequences T).craig
  have native : arithmeticConsequences B ⊢ target.standardProvability.con :=
    (arithmeticConsequences_exact target.standardProvability.con).mpr relative
  have given : searched ⊢ target.standardProvability.con := Entailment.WeakerThan.pbl native
  let : 𝗣𝗔⁻ ⪯ searched :=
    Entailment.WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ arithmeticConsequences B) inferInstance
  have transfer := arithmetical_consistency_transfer searched target given
  let : 𝗜𝚺₁ ⪯ arithmeticConsequences T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) inferInstance
  have haltingToConsistency :
      arithmeticConsequences T ⊢ (∼arithmeticHalting.val) 🡒 target.standardProvability.con := by
    have a : arithmeticConsequences T ⊢ (∼arithmeticHalting.val) 🡒 searched.consistent.val :=
      Entailment.WeakerThan.pbl calibration
    have b : arithmeticConsequences T ⊢ searched.consistent.val 🡒 target.standardProvability.con :=
      Entailment.WeakerThan.pbl transfer
    exact C_trans a b
  intro proof
  have negation (φ : ArithmeticSentence) :
      arithmeticTranslation.translate (∼φ) = ∼arithmeticTranslation.translate φ :=
    (arithmeticTranslation.translate : ArithmeticSentence →ˡᶜ SetTheorySentence).map_neg' φ
  have translated : T ⊢ arithmeticTranslation.translate (∼arithmeticHalting.val) := by
    rw [negation]
    exact proof
  have arith : arithmeticConsequences T ⊢ ∼arithmeticHalting.val :=
    (arithmeticConsequences_exact _).mpr translated
  have internal : arithmeticConsequences T ⊢ target.standardProvability.con :=
    haltingToConsistency ⨀ arith
  exact translated_craig_consistency_unprovable consistent
    ((arithmeticConsequences_exact _).mp internal)

/-- Isolate the remaining proof translation from the machine's verified
native calculus to the set theory searched by the program. -/
theorem nonhalting_unprovable_of_native_calibration (B T : SetTheory) [𝗭𝗙 ⪯ B] [𝗭𝗙 ⪯ T]
    [(arithmeticConsequences B).RE] [(arithmeticConsequences T).RE]
    (consistent : Entailment.Consistent T)
    (calibration : 𝗣𝗔 ⊢ (∼Arithmetization.nativeRefutable.val) 🡒
      (arithmeticConsequences B).craig.consistent.val)
    (relative : B ⊢ arithmeticTranslation.translate (arithmeticConsequences T).craig.standardProvability.con) :
    T ⊬ ∼setHalting :=
  nonhalting_unprovable_of_calibration B T consistent
    (C_trans Arithmetization.native_nonhalting_implies_consistency calibration) relative

theorem independence_descends {U T : SetTheory} [U ⪯ T]
    (unprovable : T ⊬ setHalting) (unrefutable : T ⊬ ∼setHalting) :
    (U ⊬ setHalting) ∧ (U ⊬ ∼setHalting) :=
  ⟨fun h => unprovable (Entailment.WeakerThan.pbl h),
    fun h => unrefutable (Entailment.WeakerThan.pbl h)⟩

end I0451
