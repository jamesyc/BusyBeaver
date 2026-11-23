module
public import I3_334Support.Search.Compiler.RegisterFile
public import I3_334Support.Arithmetic.Numerals
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem option_cast (value : Option Nat) :
    (value.map (Nat.cast : Nat → M)).getD 0 = (value.getD 0 : M) := by
  cases value <;> simp

theorem storeOf_cast (rs : List Nat) :
    storeOf (rs.map (Nat.cast : Nat → M)) = (Nat.cast : Nat → M) ∘ storeOf rs := by
  funext r
  simp [storeOf,option_cast,Function.comp_apply]

end PalomarI3380.Compiler
