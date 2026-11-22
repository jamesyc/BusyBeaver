module
public import ZF192Support.Execution.Registers.Arithmetic.Footprints
public import ZF192Support.Execution.Registers.Arithmetic.UnpairLoop
public import ZF192Support.Execution.Registers.Arithmetic.PairCore
public meta import Mathlib.Tactic.FinCases
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativePop
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def unpairState (offset:Nat) (ρ:Nat→M) (pc:Nat) (w h x y:M) : NativeSource.State M :=
 ⟨((offset+pc:Nat):M),![w,ρ 1,ρ 2,ρ 3,ρ 4,y,ρ 6,h,x]⟩
private theorem loopRows {offset : Nat} (hb : Bound offset) : NativeUnpair.Bound offset 0 where
  range := by have := hb.range; omega
  input_ne_x := by decide
  input_ne_y := by decide
  countdown := by simpa [expected] using hb.rows 0
  advanceY := hb.rows 1
  testX := hb.rows 2
  skipTransfer := hb.rows 3
  transfer := hb.transfer
  loop := hb.rows 7

theorem native_pop {offset : Nat} (hb : Bound offset) (ρ : Nat → M) (n h : M) :
    nativeReaches (unpairState offset ρ 0 n h 0 0)
      (unpairState offset ρ 11 (modelUnpairRight n) h (modelUnpairLeft n) 0) := by
  let frame := fun i => if i = 7 then h else ρ i
  have hs (pc : Nat) (w x y : M) :
      NativeUnpair.state 0 frame ((offset+pc : Nat) : M) w x y =
        unpairState offset ρ pc w h x y := by
    unfold NativeUnpair.state unpairState
    congr 1
    funext j
    fin_cases j <;> rfl
  have reached := NativeUnpair.unpair_to_input (loopRows hb) hb.restore frame n
  change nativeReaches (NativeUnpair.state 0 frame ((offset+0 : Nat) : M) n 0 0) _ at reached
  simpa only [hs] using reached

lemma native_pop_pairState {offset:Nat} (hb:Bound offset) (ρ:Nat→M) (t w:M) :
 nativeReaches (NativePair.pairState offset ρ 0 t w 0 0)
 (NativePair.pairState offset ρ 11 t (modelUnpairRight w) (modelUnpairLeft w) 0) := by
 let frame:Nat→M:=fun i=>if i=2 then t else ρ i
 have ht:=native_pop hb frame w (ρ 7)
 simpa [unpairState,NativePair.pairState,frame] using ht
lemma bound_4262 : Bound 4262 := by
 constructor
 · decide
 · decide
 · constructor <;> decide
 · constructor <;> decide
end ZF192Support.NativePop
