module
public import I3_334.Calibration.LegacyCongruence
public import I3_334.Calibration.ModelReach
public import I3_334Support.Calibration.CodedUltrafilter
public import I3_334Support.Calibration.GroundNames
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Calibration.TermWords
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A collapse of the older coded ground quotient gives a guarded
calculus proof in the same arithmetic model. -/
theorem modelDerives_of_legacyCollapse
    (collapsed : (stagedAlgebra (M := M)).constant .D = stagedAlgebra.constant .J) :
    ModelDerives (legacyConst (M := M) 1) (legacyConst 0) := by
  let a := (groundAlgebra (M := M)).constant .D
  let b := (groundAlgebra (M := M)).constant .J
  have original : Convertible (termTokens a.val) (termTokens b.val) :=
    Quotient.exact collapsed
  have related := old_convertible_agrees original 0 StackAgreement.empty
  rw [(pushesLegacy a).2,(pushesLegacy b).2] at related
  have heads := related.2 0 (by simp [Arithmetic.zero_lt_one])
  simp only [nth_adjoin_zero] at heads
  change LegacyAgreement (legacyEval (application (.constant .D) ![]).val)
    (legacyEval (application (.constant .J) ![]).val) at heads
  rw [legacyEval_application,legacyEval_application] at heads
  simpa only [legacyApplication,legacyConstant,Arithmetic.pi₁_pair] using heads.2.2.1

private theorem constant_tokens (c : Constant) (tag : Nat)
    (encoding : Encodable.encode (show PalomarI3380.Calibration.FilterLanguage.Func 0 from .constant c) = tag) :
    termTokens ((groundAlgebra (M := M)).constant c).val = legacyConst tag := by
  change termTokens (application (.constant c) ![]).val = _
  rw [application_tokens,matrixToVec_nil,flattenTokens_zero]
  change (⟪((0 : Nat) : M),((Encodable.encode
    (show PalomarI3380.Calibration.FilterLanguage.Func 0 from .constant c)) : M)⟫ : M) ∷ 0 = _
  rw [encoding]
  rfl

theorem coded_halts_of_legacyCollapse
    (collapsed : (stagedAlgebra (M := M)).constant .D = stagedAlgebra.constant .J) :
    (ArithmeticMachine.haltsDef 334 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  apply coded_halts_of_modelDerives _ _ (modelDerives_of_legacyCollapse collapsed)
  · rw [← constant_tokens .D 1 (by decide)]
    exact constD_word
  · rw [← constant_tokens .J 0 (by decide)]
    exact constJ_word

end PalomarI3334.SearchProgram
