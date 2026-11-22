module
public import ZF192Support.Execution.Registers.Commands.AX.CompareH
public import ZF192Support.Execution.Registers.Commands.AX.CompareD
public import ZF192Support.Execution.Registers.Arithmetic.ClearT
public import ZF192Support.Execution.Registers.Commands.AX.CopyDrain
public import ZF192Support.Execution.Registers.Commands.AX.Operations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeAXGate
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def frame (n l w t a d h x y:M) : Nat→M := fun j=>
 if j=0 then w else if j=1 then l else if j=2 then t else if j=3 then d else if j=4 then a else if j=5 then y else if j=6 then n else if j=7 then h else x
noncomputable def cfg (pc n l w t a d h x y:M) : NativeSource.State M :=
 ⟨pc,![w,l,t,d,a,y,n,h,x]⟩
lemma clear4201 : NativeClearT.Bound 4201 := by constructor <;> decide +kernel
lemma clear4219 : NativeClearT.Bound 4219 := by constructor <;> decide +kernel
lemma compareH (n l w t a d h x y:M) :
 nativeReaches (cfg 4191 n l w t a d h x y)
 (cfg 4203 n l w (if h=x then 0 else t) a d 0 0 y) := by
 by_cases he:h=x
 · rw [if_pos he]
   have hc:=NativeAXCompareH.native_guard_equal (frame n l w t a d h x y) h x he
   have ht:=NativeClearT.clear clear4201 (frame n l w t a d 0 0 y) t
   exact nativeReaches_trans (by simpa [frame,cfg,NativeAXCompareH.guardState] using hc)
    (by simpa [frame,cfg,NativeClearT.cfg] using ht)
 · rw [if_neg he]
   simpa [frame,cfg,NativeAXCompareH.guardState] using NativeAXCompareH.native_guard_unequal (frame n l w t a d h x y) h x he
lemma compareD (n l w t a d h x y:M) :
 nativeReaches (cfg 4209 n l w t a d h x y)
 (cfg 4221 n l w (if h=x then 0 else t) a d 0 0 y) := by
 by_cases he:h=x
 · rw [if_pos he]
   have hc:=NativeAXCompareD.native_guard_equal (frame n l w t a d h x y) h x he
   have ht:=NativeClearT.clear clear4219 (frame n l w t a d 0 0 y) t
   exact nativeReaches_trans (by simpa [frame,cfg,NativeAXCompareD.guardState] using hc)
    (by simpa [frame,cfg,NativeClearT.cfg] using ht)
 · rw [if_neg he]
   simpa [frame,cfg,NativeAXCompareD.guardState] using NativeAXCompareD.native_guard_unequal (frame n l w t a d h x y) h x he
end ZF192Support.NativeAXGate
