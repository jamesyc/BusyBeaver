module
public import ModelNativeCandidateOutcome
public import ModelSchedulerCoverage
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCommands
open ZF209.NativeSource ZF209.ModelCommands ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def summaryLiftState (code:M) : State M :=
 commandState 25 (modelUnpairLeft code) 0 0 (storeDecode (modelUnpairRight code))
lemma summaryLiftState_pair (n packed:M) : summaryLiftState (modelCantor n packed)=
 commandState 25 n 0 0 (storeDecode packed) := by
 simp only [summaryLiftState,modelUnpairLeft_pair,modelUnpairRight_pair]
noncomputable def summaryLiftGraph : ArithmeticSemiformula Nat 2 :=
 “z code. ∃n, ∃t, ∃w, ∃d, ∃h,
 !cfgFormula code n t w d h ∧ !stateGraph z 25 w 0 t d 0 0 n h 0”
lemma summaryLiftGraph_eval (ρ:Nat→M) (z code:M) :
 summaryLiftGraph.Eval ![z,code] ρ ↔ z=stateCode (summaryLiftState code) := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [summaryLiftGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,
 Empty.eq_elim,cfgFormula_eval,stateGraph_eval,numeral_eq_natCast]
 constructor
 · rintro ⟨n,t,w,d,h,rfl,hz⟩
   simpa only [summaryLiftState,commandCfgCode,modelUnpairLeft_pair,modelUnpairRight_pair,storeDecode_code,commandState] using hz
 · intro hz
   let s:=storeDecode (modelUnpairRight code)
   refine ⟨modelUnpairLeft code,s.t,s.w,s.d,s.h,(cfg_decode code).symm,?_⟩
   exact hz
lemma summary_step_native (hc:successBodyContract (M:=M)) {before after:M}
 (hs:ModelScheduler.candidateStep before after) : nativeReaches (summaryLiftState before) (summaryLiftState after) := by
 obtain ⟨n,old,out,hist,rfl,rfl,hr,he⟩:=hs
 rw [summaryLiftState_pair,summaryLiftState_pair]
 apply candidate_run_success hc n (storeDecode old) (storeDecode out) hist
 · simpa only [commandCfgCode,ModelScheduler.storeCode_decode] using hr
 · simpa only [commandCfgCode,ModelScheduler.storeCode_decode] using he
lemma summary_halt_native (hc:successBodyContract (M:=M)) {code:M} (hh:ModelScheduler.candidateHalt code) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (summaryLiftState code) stop := by
 obtain ⟨n,packed,hist,rfl,hr,he⟩:=hh
 rw [summaryLiftState_pair]
 apply candidate_run_halt hc n (storeDecode packed) hist
 · simpa only [commandCfgCode,ModelScheduler.storeCode_decode] using hr
 · exact he
end ZF209.NativeCommands
