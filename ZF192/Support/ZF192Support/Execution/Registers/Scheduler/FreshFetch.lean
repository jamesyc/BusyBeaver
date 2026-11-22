module
public import ZF192Support.Execution.Registers.Scheduler.CommandHistory
public import ZF192Support.Execution.Commands.Code
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.NativeFetch ZF192Support.ModelCommands ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem fresh_fetch_coded_command (c:Command M) (tail:M) (s:Store M) :
 nativeReaches (commandState 25 (commandCode c tail) 0 0 s) (bodyEntry c (commandCode c tail+1) tail s) := by
 have ht:=native_fetch_dispatch (commandFrame s) (commandCode c tail) 0
 simp only [if_pos rfl] at ht
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
lemma fresh_first_step (hc:successBodyContract (M:=M)) (candidate:M) (s:Store M) {after:M}
 (hs:codedCommandStep (commandCfgCode (candidate+1) s) after) :
 nativeReaches (commandState 25 candidate 0 0 s) (liftState (candidate+1) after) := by
 obtain ⟨c,tail,old,out,hb,rfl,he⟩:=hs
 have hp:=congrArg modelUnpairLeft hb
 have hv:=congrArg modelUnpairRight hb
 simp only [commandCfgCode,modelUnpairLeft_pair,modelUnpairRight_pair] at hp hv
 have hn:candidate=commandCode c tail:=add_right_cancel hp
 have hstore:s=old:=storeCode_injective hv
 subst old
 rw [hn,liftState_cfg]
 exact nativeReaches_trans (fresh_fetch_coded_command c tail s) (hc c _ tail s out he)
end ZF192Support.NativeCommands
