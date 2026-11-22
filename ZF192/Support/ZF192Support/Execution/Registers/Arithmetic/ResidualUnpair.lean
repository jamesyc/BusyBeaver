module
public import ZF192Support.Execution.Registers.Arithmetic.UnpairLoop
public meta import Mathlib.Tactic.FinCases

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.ResidualSource
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def unpairState (ρ:Nat→M) (pc w h x y:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,w,ρ 2,ρ 3,h,y,ρ 6,ρ 7,x]⟩

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem state_eq (ρ : Nat → M) (pc w h x y : M) :
    NativeUnpair.state 1 (NativeUnpair.withAccumulator 4 ρ h) pc w x y =
      unpairState ρ pc w h x y := by
  unfold NativeUnpair.state unpairState
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem loopRows : NativeUnpair.Bound 34 1 := by
  constructor <;> first | decide +kernel | (constructor <;> decide +kernel)

private theorem restoreY : NativeTransfer.Bound 42 5 1 := by
  constructor <;> decide +kernel

private theorem restoreX : NativeTransfer.Bound 45 8 4 := by
  constructor <;> decide +kernel

theorem native_unpair (ρ : Nat → M) (n : M) :
    nativeReaches (unpairState ρ 34 n 0 0 0)
      (unpairState ρ 48 (modelUnpairRight n) (modelUnpairLeft n) 0 0) := by
  simpa only [state_eq, Nat.reduceAdd, Nat.cast_ofNat, zero_add] using
    NativeUnpair.unpair_add (dest := (4 : Fin 9)) loopRows
      (by decide) (by decide) restoreY restoreX ρ n 0

end ZF192Support.ResidualSource
