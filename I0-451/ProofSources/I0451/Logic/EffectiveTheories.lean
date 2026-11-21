module
public import I0451.Logic.SetAxiomCodes
public import I0451.Logic.BerkeleyTheory
public import I0451.Logic.I0
public import I0451.Omega.CodedTranslation
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-! Equivalent recursively enumerable presentations for the searched
and target set theories. The arithmetic consequence predicates use
the same omega interpretation as the halting sentence. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open I0451.Logic.SetAssignments I0451.Omega ZF207.OmegaInterpretation ZF207.Internal.Arith
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def parameterizedExtension (extra : SetTheory) : SetTheory := parameterizedZF ∪ extra

def zfExtension (extra : SetTheory) : SetTheory := 𝗭𝗙 ∪ extra

instance (extra : SetTheory) : 𝗘𝗤 ℒₛₑₜ ⪯ parameterizedExtension extra :=
  Entailment.WeakerThan.ofSubset fun _ h => Or.inl (Or.inl (Or.inl (BasicSetTheory.equality _ h)))

instance (extra : SetTheory) : 𝗭𝗙 ⪯ zfExtension extra :=
  Entailment.WeakerThan.ofSubset fun _ h => Or.inl h

instance (extra : SetTheory) : 𝗘𝗤 ℒₛₑₜ ⪯ zfExtension extra :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙) inferInstance

instance (extra : SetTheory) [extra.RE] : (parameterizedExtension extra).RE :=
  Theory.RE.add (inferInstance : parameterizedZF.RE) inferInstance

theorem parameterizedExtension_equivalent (extra : SetTheory) (σ : SetTheorySentence) :
    parameterizedExtension extra ⊢ σ ↔ zfExtension extra ⊢ σ := by
  constructor
  · intro proof
    apply SetTheory.complete.{0}
    intro M _ _ models
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun _ h => models.models_set (.inl h)⟩
    have parameterized : M↓[ℒₛₑₜ] ⊧* parameterizedZF := parameterizedZF_of_zf
    have extend : M↓[ℒₛₑₜ] ⊧* parameterizedExtension extra := ⟨fun p h => by
      rcases h with base | added
      · exact parameterized.models_set base
      · exact models.models_set (.inr added)⟩
    exact models_of_provable extend proof
  · intro proof
    apply SetTheory.complete.{0}
    intro M _ _ models
    let : M↓[ℒₛₑₜ] ⊧* parameterizedZF := ⟨fun _ h => models.models_set (.inl h)⟩
    have zf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := zf_of_parameterizedZF
    have extend : M↓[ℒₛₑₜ] ⊧* zfExtension extra := ⟨fun p h => by
      rcases h with base | added
      · exact zf.models_set base
      · exact models.models_set (.inr added)⟩
    exact models_of_provable extend proof

theorem arithmeticalProof_exact (extra : SetTheory) (σ : ArithmeticSentence) :
    parameterizedExtension extra ⊢ readArithmetic σ ↔
      zfExtension extra ⊢ arithmeticTranslation.translate σ := by
  rw [parameterizedExtension_equivalent extra]
  constructor
  · intro proof
    apply SetTheory.complete.{0}
    intro M _ _ models
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun _ h => models.models_set (.inl h)⟩
    exact (translated_models σ).mpr ((readArithmetic_models σ).mp (models_of_provable models proof))
  · intro proof
    apply SetTheory.complete.{0}
    intro M _ _ models
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun _ h => models.models_set (.inl h)⟩
    exact (readArithmetic_models σ).mpr ((translated_models σ).mp (models_of_provable models proof))

instance (extra : SetTheory) [extra.RE] : (arithmeticConsequences (zfExtension extra)).RE := by
  let checked := (parameterizedExtension extra).craig
  have recognizable : 𝚺ᴬ₁-Predicate (fun code : Nat => Provable checked (kax omegaReader code)) := by
    have reading := omegaReaderCode_defined (W := Nat)
    have proofs := Provable.definable (V := Nat) (T := checked)
    definability
  have enumerable := (rePred_iff_sigma1.mpr recognizable).comp (Computable.encode (α := ArithmeticSentence))
  refine ⟨enumerable.of_eq fun σ => ?_⟩
  have encoded : (⌜σ⌝ : Nat) = Encodable.encode σ := by simpa using (Sentence.quote_eq_encode (V := Nat) σ)
  rw [← encoded, ← quote_readArithmetic, provable_iff_provable]
  change (parameterizedExtension extra).craig ⊢ readArithmetic σ ↔ _
  exact ⟨fun proof => (arithmeticalProof_exact extra σ).mp
      (Entailment.WeakerThan.pbl proof),
    fun proof => Entailment.WeakerThan.pbl ((arithmeticalProof_exact extra σ).mpr proof)⟩

theorem zfcI0_axioms : zfcI0 = zfExtension (𝗔𝗖 ∪ {i0SetAxiom}) := Set.union_assoc _ _ _

instance : (arithmeticConsequences zfcI0).RE := by
  rw [zfcI0_axioms]
  letI : (𝗔𝗖 ∪ {i0SetAxiom} : SetTheory).RE := .add
    (Theory.RE.ofFinite (Set.finite_singleton _)) (Theory.RE.ofFinite (Set.finite_singleton _))
  infer_instance

instance : (arithmeticConsequences berkeleyTheory).RE := by
  change (arithmeticConsequences (zfExtension {berkeleySetAxiom})).RE
  letI : ({berkeleySetAxiom} : SetTheory).RE := Theory.RE.ofFinite (Set.finite_singleton _)
  infer_instance

end I0451.Logic
