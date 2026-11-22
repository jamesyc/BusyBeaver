module
public import ZF192Support.Execution.Registers.Commands.MP.Compare
public import ZF192Support.Execution.Registers.Arithmetic.Transfer
public import ZF192Support.Execution.Registers.Commands.Boundary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeMPGuard
open ZF192Support.NativeSource ZF192Support.NativeCommands ZF192Support.NativeMPCompare ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma bound : NativeTransfer.Bound 4289 2 8 := by
 constructor <;> decide +kernel
noncomputable def frame (n l t w d h:M) : Nat→M := fun j=>
 if j=0 then w else if j=1 then l else if j=2 then t else if j=3 then d else if j=6 then n else if j=7 then h else 0
lemma transfer_state (pc n l t w d h x:M) :
 NativeTransfer.transferState 2 8 (frame n l t w d h) pc t x =
 ⟨pc,![w,l,t,d,0,0,n,h,x]⟩ := by
 unfold NativeTransfer.transferState
 congr 1
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma compare_state (pc n l w d h x:M) :
 guardState (frame n l 0 w d 0) pc h x = ⟨pc,![w,l,0,d,0,0,n,h,x]⟩ := by
 simp [guardState,frame]
theorem native_mp_guard (n l t w d h:M) :
 nativeReaches (commandState 4289 n l 0 ⟨t,w,d,h⟩)
 (commandState (if t=h then 4302 else 4328) n l 0 ⟨0,w,d,0⟩) := by
 have ht:=NativeTransfer.native_transfer bound (frame n l t w d h) t 0
 change nativeReaches _ (NativeTransfer.transferState 2 8 (frame n l t w d h) 4292 0 (0+t)) at ht
 rw [zero_add] at ht
 have hend : NativeTransfer.transferState 2 8 (frame n l t w d h) 4292 0 t = guardState (frame n l 0 w d 0) 4292 h t := by
   unfold NativeTransfer.transferState guardState
   congr 1
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
 rw [transfer_state,hend] at ht
 change nativeReaches (commandState 4289 n l 0 ⟨t,w,d,h⟩) _ at ht
 by_cases he:t=h
 · rw [if_pos he]
   have hc:=native_guard_equal (frame n l 0 w d 0) h t he.symm
   rw [compare_state] at hc
   exact nativeReaches_trans ht hc
 · rw [if_neg he]
   have hc:=native_guard_unequal (frame n l 0 w d 0) h t (Ne.symm he)
   rw [compare_state] at hc
   exact nativeReaches_trans ht hc
end ZF192Support.NativeMPGuard
