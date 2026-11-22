module
public import ZF192Support.Execution.Registers.Arithmetic.Compare

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeAXCompareH
open ZF192Support.NativeSource
export ZF192Support.NativeCompare (guardState)

private theorem rows : NativeCompare.Bound 4191 4203 := by
  constructor <;> decide

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma native_guard_equal (ρ : Nat → M) (h x : M) (he : h = x) :
    nativeReaches (guardState ρ 4191 h x) (guardState ρ 4201 0 0) :=
  NativeCompare.native_guard_equal rows ρ h x he

lemma native_guard_unequal (ρ : Nat → M) (h x : M) (he : h ≠ x) :
    nativeReaches (guardState ρ 4191 h x) (guardState ρ 4203 0 0) :=
  NativeCompare.native_guard_unequal rows ρ h x he

end ZF192Support.NativeAXCompareH
