module
public import ZF192Support.Execution.Registers.Arithmetic.Compare

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeMPCompare
open ZF192Support.NativeSource
export ZF192Support.NativeCompare (guardState)

private theorem rows : NativeCompare.Bound 4292 4328 := by
  constructor <;> decide

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma native_guard_equal (ρ : Nat → M) (h x : M) (he : h = x) :
    nativeReaches (guardState ρ 4292 h x) (guardState ρ 4302 0 0) :=
  NativeCompare.native_guard_equal rows ρ h x he

lemma native_guard_unequal (ρ : Nat → M) (h x : M) (he : h ≠ x) :
    nativeReaches (guardState ρ 4292 h x) (guardState ρ 4328 0 0) :=
  NativeCompare.native_guard_unequal rows ρ h x he

end ZF192Support.NativeMPCompare
