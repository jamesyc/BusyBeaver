module
public import I3_334Support.Arithmetic.OmegaReading
public import I3_334Support.Logic.Completeness
public import Foundation.FirstOrder.Incompleteness.StandardProvability
@[expose] public section

namespace PalomarI3380.Logic

open Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

theorem unprovable_neg_of_internal_consistency {A : ArithmeticTheory} [A.Δ₁]
    [𝗜𝚺₁ ⪯ A] [FFL.Entailment.Consistent A] {H : Formula}
    (internal : ZFCI3Provable (.imp (Neg H) (readArithmetic A.standardProvability.con)))
    (absorb : ∀ φ : ArithmeticSentence, ZFCI3Provable (readArithmetic φ) → A ⊢ φ) :
    ¬ZFCI3Provable (Neg H) := by
  intro proof
  have rule : Theory.Derives ZFCI3Axiom (.imp (Neg H) (readArithmetic A.standardProvability.con)) := internal
  exact ProvabilityAbstraction.con_unprovable (𝔅 := A.standardProvability) (absorb _ (rule.app proof))

end PalomarI3380.Logic
