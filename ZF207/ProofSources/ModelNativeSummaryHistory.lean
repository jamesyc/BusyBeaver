module
public import ModelNativeSummaryStep
public import ModelCCompilerComplete
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
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
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 have hr(a b:M):=(ModelScheduler.rootedFormula_eval ModelScheduler.candidateStepFormula (fun _ : Nat=>initial)
  ModelScheduler.candidateStep (ModelScheduler.candidateStepFormula_eval _) a b)
 simp [summarySimulationFormula,summarySimulation,nativeReaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,hr,nativeRunFormula_eval,
 ruleHead_defined.iff,summaryLiftGraph_eval,eq_comm]
noncomputable def summarySimulation_certificate (initial:M) :
 FormulaCertificate (fun _=>initial) 1 (fun v=>summarySimulation initial (v 0)) := by
 refine ⟨summarySimulationFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv];exact (summarySimulationFormula_eval initial (v 0)).symm
theorem summary_history_native (hc:successBodyContract (M:=M)) (initial:M) :
 ∀code:M,summarySimulation initial code := by
 apply (summarySimulation_certificate initial).orderInduction
 intro code ih
 change summarySimulation initial code
 intro hr
 have hp:0<code:=pos_iff_ne_zero.mpr hr.1
 have he:code=modelListCons (modelListHead code) (modelListTail code):=(modelList_reconstruct code hp).symm
 have ht:=modelListTail_lt code hp
 rw [he] at hr ⊢
 simp only [modelListHead_cons]
 have hedge:=(modelTrace_cons (ModelScheduler.rootedEdge ModelScheduler.candidateStep initial)
  (modelListHead code) (modelListTail code)).mp hr.2
 by_cases hz:modelListTail code=0
 · have ha:modelListHead code=initial:=by simpa [ModelScheduler.rootedEdge,hz] using hedge.2
   rw [ha];exact nativeReaches_refl _
 · have prev:ModelScheduler.rooted ModelScheduler.candidateStep initial (modelListTail code):=⟨hz,hedge.1⟩
   have step:ModelScheduler.candidateStep (modelListHead (modelListTail code)) (modelListHead code):=by
    simpa [ModelScheduler.rootedEdge,hz] using hedge.2
   exact nativeReaches_trans (ih _ ht prev) (summary_step_native hc step)
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
 (h:ZF207.ModelCommands.compilable (1:M)) (store:M) :
 ∃stop:State M,stop.pc=10 ∧ nativeReaches (commandState 25 2 0 0 (storeDecode store)) stop := by
 simpa only [summaryLiftState_pair] using summary_halts_native hc (modelCantor 2 store)
  (literalCRefutation_summary_halts h store)
end ZF207.NativeCommands
