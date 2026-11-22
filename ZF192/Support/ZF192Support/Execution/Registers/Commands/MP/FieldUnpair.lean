module
public import ZF192Support.Execution.Registers.Arithmetic.UnpairLoop
public meta import Mathlib.Tactic.FinCases

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.MPFieldSource
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def unpairState (ρ:Nat→M) (pc w h x y:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,w,ρ 2,h,ρ 4,y,ρ 6,ρ 7,x]⟩

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem state_eq (ρ : Nat → M) (pc w h x y : M) :
    NativeUnpair.state 1 (NativeUnpair.withAccumulator 3 ρ h) pc w x y =
      unpairState ρ pc w h x y := by
  unfold NativeUnpair.state unpairState
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem loopRows : NativeUnpair.Bound 4222 1 := by
  constructor <;> first | decide +kernel | (constructor <;> decide +kernel)

private theorem restoreY : NativeTransfer.Bound 4230 5 1 := by
  constructor <;> decide +kernel

private theorem restoreX : NativeTransfer.Bound 4233 8 3 := by
  constructor <;> decide +kernel

theorem native_unpair_add (ρ : Nat → M) (n h : M) :
    nativeReaches (unpairState ρ 4222 n h 0 0)
      (unpairState ρ 4236 (modelUnpairRight n) (h + modelUnpairLeft n) 0 0) := by
  simpa only [state_eq, Nat.reduceAdd, Nat.cast_ofNat] using
    NativeUnpair.unpair_add (dest := (3 : Fin 9)) loopRows
      (by decide) (by decide) restoreY restoreX ρ n h

theorem native_unpair (ρ : Nat → M) (n : M) :
    nativeReaches (unpairState ρ 4222 n 0 0 0)
      (unpairState ρ 4236 (modelUnpairRight n) (modelUnpairLeft n) 0 0) := by
  simpa only [zero_add] using native_unpair_add ρ n 0

end ZF192Support.MPFieldSource
