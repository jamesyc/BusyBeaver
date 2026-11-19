module
public import ModelCMPCompilation
public import ModelSchedulerCoverage
public import ModelSchedulerCandidateBoundary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation ZF207.MM0ModelReplay ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem ctrace_compiler (p:M) (h:modelTrace modelCRule p) : compilerInvariant p :=
 compilerInvariant_of_closures modelCAxiom_compilable modelMP_compilable modelGen_compilable p h
/-- An internal C-trace containing the falsity code `1` makes `1` compilable. -/
theorem refutation_compilable (p:M) (hp:modelTrace modelCRule p) (h1:modelMember 1 p) :
 compilable (1:M) := ctrace_compiler p hp 1 h1
/-- A single internally coded AX-first candidate halts from EVERY retained
store; the candidate itself may be nonstandard. -/
theorem literalCRefutation_uniform_candidate (h:compilable (1:M)) :
 ∃candidate:M,2≤candidate ∧ ∀s:Store M,∃hist:M,
 runHistory (candidateEntry candidate s) hist ∧ haltAt (modelListHead hist) := by
 obtain ⟨word,hw⟩ := h
 let stop:=commandCode (Command.shift (M:=M)) 0+1
 let body:=programAppend word stop
 let rest:=macroPointer (List.replicate 8 (Command.shift (M:=M))++[.mp 0]) body
 let candidate:=commandCode (.ax 0 0 0) rest
 refine ⟨candidate,ax_candidate_bound _ _ _ _,?_⟩
 intro s
 let initial:=candidateEntry candidate s
 have hstart:modelListHead (modelListCons initial 0)=commandCfgCode (macroPointer modelPUSH body) s := by
  rw [modelListHead_cons]; rfl
 obtain ⟨phist,hpr,hpo⟩ := macro_history modelPUSH body s initial (modelListCons initial 0)
  (runHistory_singleton _) hstart
 have hphead:modelListHead phist=commandCfgCode body ⟨0,modelCantor s.t s.w,0,0⟩ := by
  cases s; simpa only [push_eval] using hpo
 obtain ⟨hist,hr,ho⟩ := hw 0 (modelCantor s.t s.w)
 obtain ⟨hreb,hend⟩ := rebase_run_result word stop ⟨0,modelCantor s.t s.w,0,0⟩
  ⟨1,modelCantor s.t s.w,0,0⟩ hist hr ho
 obtain ⟨joined,hjr,hjh⟩ := command_history_concat _ _ _ phist hreb hpr hphead
 refine ⟨joined,hjr,?_⟩
 rw [hjh]
 rcases hend with hh|he
 · exact hh
 · rw [he]
   exact ⟨0,⟨1,modelCantor s.t s.w,0,0⟩,rfl,by simp⟩
/-- A compilable falsity code reaches a halting candidate in the retained-store summary
scheduler starting at 2. Native/physical simulation is a separate obligation. -/
theorem literalCRefutation_summary_halts (h:compilable (1:M)) (store:M) :
 ModelScheduler.halts (modelCantor (2:M) store) := by
 obtain ⟨candidate,hbound,huniform⟩ := literalCRefutation_uniform_candidate h
 have he: (2:M)+t46 candidate 2=candidate := p860 2 candidate ((literalLe_order _ _).mpr hbound)
 apply ModelScheduler.uniform_candidate_covered (2:M) (t46 candidate 2) store
 intro s
 obtain ⟨hist,hr,hh⟩ := huniform (storeDecode s)
 refine ⟨candidate,s,hist,?_,?_,hh⟩
 · rw [he]
 · simpa only [candidateEntry,commandCfgCode,ModelScheduler.storeCode_decode] using hr
end ZF207.ModelCommands
