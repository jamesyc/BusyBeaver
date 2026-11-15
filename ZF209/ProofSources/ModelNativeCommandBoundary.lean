module
public import ModelNativeFetchDispatch
public import ModelCommandCode
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCommands
open ZF209.NativeSource ZF209.NativeFetch ZF209.ModelCommands ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def commandState (pc n l a:M) (s:Store M) : NativeSource.State M :=
 ⟨pc,![s.w,l,s.t,s.d,a,0,n,s.h,0]⟩
noncomputable def commandFrame (s:Store M) : Nat→M := fun i=>if i=0 then s.w else if i=2 then s.t else if i=3 then s.d else if i=7 then s.h else 0
noncomputable def bodyEntry (c:Command M) (n tail:M) (s:Store M) : NativeSource.State M :=
 match c with
 | .shift => commandState 4329 n tail 0 s
 | .mp x => commandState 4222 n (modelCantor x tail) 0 s
 | .ax a x y => commandState 50 n (modelCantor y (modelCantor x tail)) a s
/-- Exact front-end parser boundary for the SAME coded command used by the internal compiler.
MP and AX fields remain in L to be consumed by the native command bodies. -/
theorem fetch_coded_command (c:Command M) (n tail:M) (s:Store M) :
 nativeReaches (commandState 25 n (commandCode c tail+1) 0 s) (bodyEntry c n tail s) := by
 have ht:=native_fetch_dispatch (commandFrame s) n (commandCode c tail+1)
 have hn:commandCode c tail+1≠0:=by simp
 rw [if_neg hn,modelPredecessor_succ] at ht
 have hp0:modelPredecessor (0:M)=0 := by
  symm; apply (predecessorGraph_value _ _).mp
  exact (predecessorGraph_eval _ _).mpr (Or.inl ⟨rfl,rfl⟩)
 cases c with
 | shift => simpa [fetchStart,fetchState,cleanFrame,commandFrame,commandState,commandEntry,bodyEntry,commandCode,
    modelUnpairLeft_pair,modelUnpairRight_pair,dispatchTarget,hp0] using ht
 | mp x =>
   have hp1:modelPredecessor (1:M)=0:=by simpa only [zero_add] using modelPredecessor_succ (0:M)
   simpa [fetchStart,fetchState,cleanFrame,commandFrame,commandState,commandEntry,bodyEntry,commandCode,
    modelUnpairLeft_pair,modelUnpairRight_pair,dispatchTarget,hp0,hp1] using ht
 | ax a x y =>
   have h0:a+2≠(0:M):=ne_of_gt (lt_of_lt_of_le (by norm_num : (0:M)<2) (le_add_self))
   have h1:a+2≠(1:M):=ne_of_gt (lt_of_lt_of_le (by norm_num : (1:M)<2) (le_add_self))
   have he:a+2=(a+1)+1:=by rw [add_assoc]; norm_num
   simpa [fetchStart,fetchState,cleanFrame,commandFrame,commandState,commandEntry,bodyEntry,commandCode,
    modelUnpairLeft_pair,modelUnpairRight_pair,dispatchTarget,h0,h1,he,modelPredecessor_succ] using ht
end ZF209.NativeCommands
