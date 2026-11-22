module
public import ZF192Support.Execution.Registers.Scheduler.FreshHistory
public import ZF192Support.Execution.Commands.Scheduler.CandidateSummary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma candidate_run_success (hc:successBodyContract (M:=M)) (candidate:M) (s out:Store M) (hist:M)
 (hr:runHistory (commandCfgCode (candidate+1) s) hist)
 (he:modelListHead hist=commandCfgCode 0 out) :
 nativeReaches (commandState 25 candidate 0 0 s) (commandState 25 (candidate+1) 0 0 out) := by
 rcases fresh_history_native hc candidate s hist hr with hfirst|hprefix
 · have hpc:=congrArg modelUnpairLeft (he.symm.trans hfirst)
   simp only [commandCfgCode,modelUnpairLeft_pair] at hpc
   exact False.elim ((by simp : (0:M)≠candidate+1) hpc)
 · simpa only [he,liftState_cfg] using hprefix
lemma coded_halt_native (n code:M) (hh:haltAt code) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (liftState n code) stop := by
 obtain ⟨tail,s,rfl,he⟩:=hh
 refine ⟨shiftStop n tail s,rfl,?_⟩
 rw [liftState_cfg]
 exact nativeReaches_trans (fetch_coded_command .shift n tail s) (shift_body_halt n tail s he)
lemma fresh_halt_native (candidate:M) (s:Store M) (hh:haltAt (commandCfgCode (candidate+1) s)) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (commandState 25 candidate 0 0 s) stop := by
 obtain ⟨tail,old,hb,he⟩:=hh
 have hp:=congrArg modelUnpairLeft hb
 have hv:=congrArg modelUnpairRight hb
 simp only [commandCfgCode,modelUnpairLeft_pair,modelUnpairRight_pair] at hp hv
 have hn:candidate=commandCode .shift tail:=add_right_cancel hp
 have hstore:s=old:=storeCode_injective hv
 subst old
 rw [hn]
 exact ⟨shiftStop (commandCode .shift tail+1) tail s,rfl,
  nativeReaches_trans (fresh_fetch_coded_command .shift tail s) (shift_body_halt _ _ _ he)⟩
lemma candidate_run_halt (hc:successBodyContract (M:=M)) (candidate:M) (s:Store M) (hist:M)
 (hr:runHistory (commandCfgCode (candidate+1) s) hist) (hh:haltAt (modelListHead hist)) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (commandState 25 candidate 0 0 s) stop := by
 rcases fresh_history_native hc candidate s hist hr with hfirst|hprefix
 · rw [hfirst] at hh
   exact fresh_halt_native candidate s hh
 · obtain ⟨stop,hpc,hs⟩:=coded_halt_native (candidate+1) _ hh
   exact ⟨stop,hpc,nativeReaches_trans hprefix hs⟩
end ZF192Support.NativeCommands
