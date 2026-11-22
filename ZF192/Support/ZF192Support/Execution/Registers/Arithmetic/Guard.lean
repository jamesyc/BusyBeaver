module
public import ZF192Support.Execution.Registers.Arithmetic.Compare

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeGuard
open ZF192Support.NativeSource
export ZF192Support.NativeCompare (guardState)

private theorem rows : NativeCompare.Bound 0 11 := by
  constructor <;> decide

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma native_guard_equal (ρ : Nat → M) (h x : M) (he : h = x) :
    nativeReaches (guardState ρ 0 h x) (guardState ρ 10 0 0) :=
  NativeCompare.native_guard_equal rows ρ h x he

lemma native_guard_unequal (ρ : Nat → M) (h x : M) (he : h ≠ x) :
    nativeReaches (guardState ρ 0 h x) (guardState ρ 11 0 0) :=
  NativeCompare.native_guard_unequal rows ρ h x he

end ZF192Support.NativeGuard
