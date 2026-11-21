module
public import I0451.IndependenceStatement
public import I0451.Logic.NativeBerkeley
public import I0451.Omega.NativeTransfer

/-! The conditional independence argument for the literal 451-state
machine. The relative consistency input is a proof in the Berkeley
theory, as in the source argument. -/
@[expose] public section
namespace I0451

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open I0451.Logic I0451.Omega I0451.Arithmetization ZF207.OmegaInterpretation
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

private theorem berkeley_reading {σ : ArithmeticSentence}
    (proof : berkeleyTheory ⊢ arithmeticTranslation.translate σ) :
    berkeleyTheory ⊢ readArithmetic σ := by
  apply SetTheory.complete.{0}
  intro V _ _ _
  let : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := berkeleyTheory) inferInstance
  exact (readArithmetic_models σ).mpr ((translated_models σ).mp (models_of_provable inferInstance proof))

theorem nativeArithmetic_absorbs_berkeley {σ : ArithmeticSentence}
    (proof : berkeleyTheory ⊢ arithmeticTranslation.translate σ) :
    nativeArithmeticTheory ⊢ σ :=
  nativeArithmetic_theorem_of_compiled
    (nativeSet_theorem_compiles (V := Nat) (Entailment.WeakerThan.pbl (berkeley_reading proof)))

private instance : 𝗣𝗔 ⪯ nativeArithmeticTheory :=
  WeakerThan.ofAxm! fun h => nativeArithmetic_absorbs_berkeley
    (WeakerThan.pbl (𝓢 := (𝗭𝗙 : SetTheory)) (pa_proof_to_zf (Entailment.by_axm h)))

set_option maxHeartbeats 1500000 in
theorem literal_nonhalting_implies_native_consistency :
    𝗣𝗔 ⊢ (∼arithmeticHalting.val) 🡒 nativeArithmeticTheory.consistent.val := by
  apply Arithmetic.complete.{0} 𝗣𝗔 _
  intro M _ _
  have implication : ¬ arithmeticHalting.val.Evalb (![] : Fin 0 → M) →
      ¬ Bootstrapping.Provable nativeArithmeticTheory (^⊥ : M) := by
    intro never refutation
    have native := native_arithmetic_refutation_translates refutation
    exact never (native_refutation_implies_halt
      (nativeRefutable_eval.mpr native))
  have consistencyPolicy : nativeArithmeticTheory.consistent.val.Evalb (![] : Fin 0 → M) ↔
      ¬ Bootstrapping.Provable nativeArithmeticTheory (^⊥ : M) := by
    simpa only [Theory.Consistent, FirstOrder.Sentence.quote_falsum] using
      (consistent.defined (T := nativeArithmeticTheory) (V := M))
  simpa only [models_iff, Semiformula.Realize, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.arrow_eq, LogicalConnective.Prop.neg_eq,
    ← Semiformula.Evalb.eq_1, consistencyPolicy] using implication

attribute [local irreducible] i0Consistency

set_option maxHeartbeats 1500000 in
theorem i0_nonhalting_unprovable (consistent : Entailment.Consistent zfcI0)
    (relative : WoodinConsistency) : zfcI0 ⊬ ∼setHalting := by
  let : 𝗣𝗔⁻ ⪯ nativeArithmeticTheory :=
    WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗣𝗔) inferInstance
  have given : nativeArithmeticTheory ⊢ i0ArithmeticTheory.standardProvability.con :=
    nativeArithmetic_absorbs_berkeley (by simpa only [WoodinConsistency, i0Consistency] using relative)
  have transfer := arithmetical_consistency_transfer nativeArithmeticTheory i0ArithmeticTheory given
  have PAtransfer : 𝗣𝗔 ⊢ nativeArithmeticTheory.consistent.val 🡒 i0ArithmeticTheory.standardProvability.con :=
    WeakerThan.pbl transfer
  have internal : 𝗣𝗔 ⊢ (∼arithmeticHalting.val) 🡒 i0ArithmeticTheory.standardProvability.con :=
    C_trans literal_nonhalting_implies_native_consistency PAtransfer
  intro refutes
  have arithmetic : arithmeticConsequences zfcI0 ⊢ ∼arithmeticHalting.val := by
    apply (arithmeticConsequences_exact _).mpr
    have negation (φ : ArithmeticSentence) :
        arithmeticTranslation.translate (∼φ) = ∼arithmeticTranslation.translate φ :=
      (arithmeticTranslation.translate : ArithmeticSentence →ˡᶜ SetTheorySentence).map_neg' φ
    rw [negation]
    exact refutes
  have consistency : arithmeticConsequences zfcI0 ⊢ i0ArithmeticTheory.standardProvability.con :=
    WeakerThan.pbl internal ⨀ arithmetic
  exact translated_craig_consistency_unprovable consistent
    ((arithmeticConsequences_exact _).mp consistency)

/-- The literal machine never halts under the Berkeley consistency
hypothesis. Halting and nonhalting are each unprovable in ZFC + I₀
and hence also in ZF with the same I₀ axiom. -/
theorem exact451_independence (berkeley : Entailment.Consistent berkeleyTheory)
    (sound : ArithmeticSigmaOneSound zfcI0) (relative : WoodinConsistency) :
    (¬ Halts literal (blank 0)) ∧
      ((zfcI0 ⊬ setHalting) ∧ (zfcI0 ⊬ ∼setHalting)) ∧
      ((zfI0 ⊬ setHalting) ∧ (zfI0 ⊬ ∼setHalting)) := by
  have never := literal_nonhalting_of_berkeley_consistency berkeley
  have noHaltProof := halting_unprovable sound never
  have noNonhaltProof := i0_nonhalting_unprovable sound.consistent relative
  exact ⟨never, ⟨noHaltProof,noNonhaltProof⟩, independence_descends noHaltProof noNonhaltProof⟩

end I0451
