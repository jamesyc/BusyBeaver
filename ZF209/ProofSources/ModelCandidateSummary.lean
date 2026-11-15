module
public import ModelRootedRelationHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelScheduler
open ZFR.ArithmeticRepresentation ZF209.ModelCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- An edge contains a genuine command-history witness, preserving the whole
returned store. This is a scheduler summary, not a native instruction step. -/
def candidateStep (before after:M) : Prop := ∃n s out hist:M,
 before=modelCantor n s ∧ after=modelCantor (n+1) out ∧
 runHistory (modelCantor (n+1) s) hist ∧ modelListHead hist=modelCantor 0 out
def candidateHalt (state:M) : Prop := ∃n s hist:M,
 state=modelCantor n s ∧ runHistory (modelCantor (n+1) s) hist ∧ haltAt (modelListHead hist)
noncomputable def candidateStepFormula : ArithmeticSemiformula Nat 2 :=
 “before after. ∃n, ∃s, ∃out, ∃hist, ∃initial, ∃last,
 !exactCantorGraph before n s ∧ !exactCantorGraph after (n+1) out ∧
 !exactCantorGraph initial (n+1) s ∧ !exactCantorGraph last 0 out ∧
 !runFormula initial hist ∧ !listHeadGraph last hist”
noncomputable def candidateHaltFormula : ArithmeticSemiformula Nat 1 :=
 “state. ∃n, ∃s, ∃hist, ∃initial, ∃last,
 !exactCantorGraph state n s ∧ !exactCantorGraph initial (n+1) s ∧
 !runFormula initial hist ∧ !listHeadGraph last hist ∧ !haltFormula last”
lemma candidateStepFormula_eval (ρ:Nat→M) (a b:M) :
 candidateStepFormula.Eval ![a,b] ρ ↔ candidateStep a b := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [candidateStepFormula,candidateStep,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,hc,runFormula_eval,ruleHead_defined.iff,eq_comm]
lemma candidateHaltFormula_eval (ρ:Nat→M) (a:M) :
 candidateHaltFormula.Eval ![a] ρ ↔ candidateHalt a := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [candidateHaltFormula,candidateHalt,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,hc,runFormula_eval,ruleHead_defined.iff,haltFormula_eval]
lemma storeCode_decode (s:M) : storeCode (storeDecode s)=s := by
 simp only [storeCode,storeDecode,modelUnpair_reconstruct]
lemma candidate_totality (n s:M) : candidateHalt (modelCantor n s) ∨
 ∃out:M,candidateStep (modelCantor n s) (modelCantor (n+1) out) := by
 let initial:=modelCantor (n+1) s
 have hi:initial=commandCfgCode (n+1) (storeDecode s) := by
  simp only [initial,commandCfgCode,storeCode_decode]
 obtain ⟨hist,hr,hh⟩ := command_totality (n+1) (storeDecode s) initial (modelListCons initial 0)
  (runHistory_singleton initial) (by rw [modelListHead_cons];exact hi)
 rcases hh with hhalt|⟨out,hout⟩
 · exact Or.inl ⟨n,s,hist,rfl,hr,hhalt⟩
 · exact Or.inr ⟨storeCode out,n,s,storeCode out,hist,rfl,rfl,hr,hout⟩
end ZF209.ModelScheduler
