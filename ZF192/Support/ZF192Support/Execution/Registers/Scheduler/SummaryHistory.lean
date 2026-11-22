module
public import ZF192Support.Execution.Registers.Scheduler.SummaryStep
public import ZF192Support.Execution.Commands.Compiler.Complete
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def summarySimulation (initial code:M) : Prop := ModelScheduler.rooted ModelScheduler.candidateStep initial code →
 nativeReaches (summaryLiftState initial) (summaryLiftState (modelListHead code))
noncomputable def summarySimulationFormula : ArithmeticSemiformula Nat 1 :=
 “code. !(ModelScheduler.rootedFormula ModelScheduler.candidateStepFormula) &0 code →
 ∃first, ∃last, ∃target,
 !summaryLiftGraph first &0 ∧ !listHeadGraph last code ∧ !summaryLiftGraph target last ∧
 ∀root, ∀hist, (!nativeRunFormula root hist ∧ !listHeadGraph first hist) →
 ∃out, !nativeRunFormula root out ∧ !listHeadGraph target out”
lemma summarySimulationFormula_eval (initial code:M) :
 summarySimulationFormula.Eval ![code] (fun _=>initial) ↔ summarySimulation initial code := by
 have hr(a b:M):=(ModelScheduler.rootedFormula_eval ModelScheduler.candidateStepFormula (fun _ : Nat=>initial)
  ModelScheduler.candidateStep (ModelScheduler.candidateStepFormula_eval _) a b)
 simp [summarySimulationFormula,summarySimulation,nativeReaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,hr,nativeRunFormula_eval,
 ruleHead_defined.iff,summaryLiftGraph_eval,eq_comm]
theorem summary_history_native (hc : successBodyContract (M := M)) (initial : M) :
    ∀ code : M, summarySimulation initial code := by
  exact ModelScheduler.rooted_induction ModelScheduler.candidateStep initial
    summarySimulationFormula (fun _ => initial)
    (fun last => nativeReaches (summaryLiftState initial) (summaryLiftState last))
    (summarySimulationFormula_eval initial) (nativeReaches_refl _)
    (fun _ _ hs hr => nativeReaches_trans hr (summary_step_native hc hs))
theorem summary_halts_native (hc:successBodyContract (M:=M)) (initial:M) (h:ModelScheduler.halts initial) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (summaryLiftState initial) stop := by
 obtain ⟨s,⟨hist,hr,he⟩,hh⟩:=h
 have hs:=summary_history_native hc initial hist hr
 rw [he] at hs
 obtain ⟨stop,hpc,ht⟩:=summary_halt_native hc hh
 exact ⟨stop,hpc,nativeReaches_trans hs ht⟩
/-- Exact internally coded C refutation implies native halt, conditional ONLY on
remaining native successful-command bodies. Not yet physical binary simulation. -/
theorem literalCRefutation_native_halt (hc:successBodyContract (M:=M))
 (h:ZF192Support.ModelCommands.compilable (1:M)) (store:M) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (commandState 25 2 0 0 (storeDecode store)) stop := by
 simpa only [summaryLiftState_pair] using summary_halts_native hc (modelCantor 2 store)
  (literalCRefutation_summary_halts h store)
end ZF192Support.NativeCommands
