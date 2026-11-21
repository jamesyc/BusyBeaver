module
public import I0451.Omega.ConcreteArithmeticProofTransport
public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-! The arithmetic consequences of a set theory extending ZF. Exact
proof transport in both directions identifies their external
consistency and provides the Gödel II conclusion for a Craig presentation. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open ZF207.OmegaInterpretation

def arithmeticConsequences (T : SetTheory) : ArithmeticTheory :=
  {σ | T ⊢ arithmeticTranslation.translate σ}

variable {T : SetTheory} [𝗭𝗙 ⪯ T]

instance arithmeticConsequences_extends_arithmetic : 𝗣𝗔 ⪯ arithmeticConsequences T :=
  WeakerThan.ofAxm! fun {σ} belongs =>
    Entailment.by_axm (show T ⊢ arithmeticTranslation.translate σ from
      Entailment.WeakerThan.pbl (pa_proof_to_zf (Entailment.by_axm belongs)))

theorem translated_models {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (σ : ArithmeticSentence) :
    V↓[ℒₛₑₜ] ⊧ arithmeticTranslation.translate σ ↔
      (arithmeticTranslation.Model V)↓[ℒₒᵣ] ⊧ σ := by
  have h := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V) (σ := σ)
  rw [interpreted_structure_eq_standard (V := V)] at h
  exact h

theorem arithmeticConsequences_exact (σ : ArithmeticSentence) :
    arithmeticConsequences T ⊢ σ ↔ T ⊢ arithmeticTranslation.translate σ := by
  constructor
  · intro proof
    letI : 𝗘𝗤 _ ⪯ T := WeakerThan.trans ((inferInstance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙)) inferInstance
    apply SetTheory.complete.{0}
    intro V _ _ _
    letI : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := T) inferInstance
    have omega : (arithmeticTranslation.Model V)↓[ℒₒᵣ] ⊧* arithmeticConsequences T := by
      constructor
      intro φ h
      exact (translated_models φ).mp (models_of_provable inferInstance (show T ⊢ arithmeticTranslation.translate φ from h))
    exact (translated_models σ).mpr (models_of_provable omega proof)
  · intro proof
    exact Entailment.by_axm (show σ ∈ arithmeticConsequences T from proof)

theorem arithmeticConsequences_consistent :
    Entailment.Consistent (arithmeticConsequences T) ↔ Entailment.Consistent T := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr (arithmeticConsequences_exact ⊥)

theorem translated_craig_consistency_unprovable
    [(arithmeticConsequences T).RE] (consistent : Entailment.Consistent T) :
    T ⊬ arithmeticTranslation.translate (arithmeticConsequences T).craig.standardProvability.con := by
  let : Entailment.Consistent (arithmeticConsequences T) :=
    arithmeticConsequences_consistent.mpr consistent
  let : 𝗜𝚺₁ ⪯ arithmeticConsequences T :=
    WeakerThan.trans ((inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔)) inferInstance
  intro proof
  let target := (arithmeticConsequences T).craig
  let : 𝗜𝚺₁ ⪯ target :=
    WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ arithmeticConsequences T) inferInstance
  let : 𝗣𝗔⁻ ⪯ target :=
    WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗜𝚺₁) inferInstance
  have arithmetic : arithmeticConsequences T ⊢ target.standardProvability.con :=
    (arithmeticConsequences_exact _).mpr proof
  exact ProvabilityAbstraction.con_unprovable (𝔅 := target.standardProvability)
    (WeakerThan.pbl arithmetic)

end I0451.Omega
