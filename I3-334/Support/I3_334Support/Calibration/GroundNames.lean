module
public import I3_334Support.Calibration.GroundTerms
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceWords (emitVector)
open ArithmeticMachine.SourceCantor (pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem triangle_one : ArithmeticMachine.SourceCantor.triangleValue (1 : M)=1 := by
  simpa only [zero_add,ArithmeticMachine.SourceCantor.triangle_zero] using
    ArithmeticMachine.SourceCantor.triangle_succ (0 : M)

theorem triangle_two : ArithmeticMachine.SourceCantor.triangleValue (2 : M)=3 := by
  rw [← one_add_one_eq_two,ArithmeticMachine.SourceCantor.triangle_succ,triangle_one,
    one_add_one_eq_two,two_add_one_eq_three]

theorem constD_word : termWord ((groundAlgebra (M := M)).constant .D).val=4 := by
  change emitVector (termTokens (application (.constant .D) ![]).val) 0 = _
  rw [application_tokens]
  have code : (⌜(show FilterLanguage.Func 0 from FunctionSymbol.constant .D)⌝ : M) = 1 := by
    change ((1 : Nat) : M) = 1
    exact Nat.cast_one
  simp [code,ArithmeticMachine.SourceWords.cons,pairValue,
    triangle_one,triangle_two,one_add_one_eq_two,three_add_one_eq_four]

theorem constJ_word : termWord ((groundAlgebra (M := M)).constant .J).val=1 := by
  change emitVector (termTokens (application (.constant .J) ![]).val) 0 = _
  rw [application_tokens]
  have code : (⌜(show FilterLanguage.Func 0 from FunctionSymbol.constant .J)⌝ : M) = 0 := rfl
  simp [code,ArithmeticMachine.SourceWords.cons,pairValue,triangle_one]

end PalomarI3380.Calibration.TermWords
