module
public import ZF192Support.Execution.Commands.Scheduler.CandidateSummary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelScheduler
open ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def reaches (initial state:M) : Prop := ∃hist:M,rooted candidateStep initial hist ∧ modelListHead hist=state
def halts (initial:M) : Prop := ∃state:M,reaches initial state ∧ candidateHalt state
noncomputable def reachesFormula : ArithmeticSemiformula Nat 2 :=
 “initial state. ∃hist, !(rootedFormula candidateStepFormula) initial hist ∧ !listHeadGraph state hist”
noncomputable def haltsFormula : ArithmeticSemiformula Nat 1 :=
 “initial. ∃state, !reachesFormula initial state ∧ !candidateHaltFormula state”
lemma reachesFormula_eval (ρ:Nat→M) (initial state:M) :
 reachesFormula.Eval ![initial,state] ρ ↔ reaches initial state := by
 have hr (a b:M) := rootedFormula_eval candidateStepFormula ρ candidateStep (candidateStepFormula_eval ρ) a b
 simp [reachesFormula,reaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,hr,ruleHead_defined.iff,eq_comm]
lemma haltsFormula_eval (ρ:Nat→M) (initial:M) : haltsFormula.Eval ![initial] ρ ↔ halts initial := by
 simp [haltsFormula,halts,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton,
 reachesFormula_eval,candidateHaltFormula_eval]
def progress (start initial n:M) : Prop := halts initial ∨ ∃s:M,reaches initial (modelCantor (start+n) s)
noncomputable def progressFormula : ArithmeticSemiformula Nat 1 :=
 “n. !haltsFormula &1 ∨ ∃s, ∃state, !exactCantorGraph state (&0+n) s ∧ !reachesFormula &1 state”
lemma progressFormula_eval (ρ:Nat→M) (n:M) :
 progressFormula.Eval ![n] ρ ↔ progress (ρ 0) (ρ 1) n := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp [progressFormula,progress,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,hc,reachesFormula_eval,haltsFormula_eval]
noncomputable def progress_certificate (start initial:M) :
 FormulaCertificate (fun i=>if i=0 then start else initial) 1 (fun v=>progress start initial (v 0)) := by
 refine ⟨progressFormula,?_⟩
 intro v
 rw [Matrix.fun_eq_vec_one v]
 simpa using (progressFormula_eval (fun i=>if i=0 then start else initial) (v 0)).symm
lemma reaches_self (initial:M) : reaches initial initial :=
 ⟨modelListCons initial 0,rooted_singleton _ _,modelListHead_cons _ _⟩
lemma reaches_extend {initial a b:M} (h:reaches initial a) (hs:candidateStep a b) : reaches initial b := by
 obtain ⟨hist,hr,hh⟩ := h
 exact ⟨modelListCons b hist,rooted_extend _ hr (by rw [hh];exact hs),modelListHead_cons _ _⟩
/-- PA induction over candidate count, retaining each returned store exactly.
The trace is of candidate summaries backed by command histories, not native steps. -/
theorem scheduler_progress (start store:M) : ∀n:M,progress start (modelCantor start store) n := by
 apply (progress_certificate start (modelCantor start store)).induction
 · change progress start (modelCantor start store) 0
   exact Or.inr ⟨store,by simpa only [add_zero] using reaches_self (modelCantor start store)⟩
 · intro n ih
   change progress start (modelCantor start store) (n+1)
   change progress start (modelCantor start store) n at ih
   rcases ih with hh|⟨s,hr⟩
   · exact Or.inl hh
   · rcases candidate_totality (start+n) s with hh|⟨out,ho⟩
     · exact Or.inl ⟨_,hr,hh⟩
     · exact Or.inr ⟨out,by simpa only [add_assoc] using reaches_extend hr ho⟩
theorem uniform_candidate_covered (start offset store:M)
 (h:∀s:M,candidateHalt (modelCantor (start+offset) s)) : halts (modelCantor start store) := by
 rcases scheduler_progress start store offset with hh|⟨s,hr⟩
 · exact hh
 · exact ⟨_,hr,h s⟩
end ZF192Support.ModelScheduler
