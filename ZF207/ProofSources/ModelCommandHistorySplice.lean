module
public import ModelHistorySplice
public import ModelCommandRun
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation ZF207.ModelCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def rootedRunFormula (i:Nat) : ArithmeticSemiformula Nat 1 :=
 Rewriting.app (Rew.bind (L:=ℒₒᵣ) ![&i,#0] (fun j=> &(j+2))) runFormula
lemma rootedRunFormula_eval (i:Nat) (ρ:Nat→M) (n:M) :
 (rootedRunFormula i).Eval ![n] ρ ↔ runHistory (ρ i) n := by
 have hv : (fun _:Fin 1=>n)=![n] := by funext j; have hj:j=0:=Subsingleton.elim _ _; subst j; rfl
 rw [rootedRunFormula,Semiformula.eval_rew]
 simpa [Function.comp_def,Matrix.comp_vecCons',hv] using
  runFormula_eval (fun j=>ρ (j+2)) (ρ i) n
lemma runHistory_cons_nonempty (initial a t:M) (ht:t≠0) :
 runHistory initial (modelListCons a t) ↔
 runHistory initial t ∧ codedCommandStep (modelListHead t) a := by
 simp [runHistory,modelTrace_cons,runEdge,ht,cons_ne_zero]
/-- Splice a model-sized command history prefix onto a compatible earlier run.
The resulting history retains the earlier run's actual oldest initial state.
This is history splicing, not concatenation of the variable-arity command words. -/
lemma command_history_splice (first initial n s b:M)
 (hf:runHistory first (append n (modelListCons s 0)))
 (hb:runHistory initial b) (hhead:modelListHead b=s) :
 runHistory initial (append n b) := by
 let ρ:Nat→M := fun i=>if i=0 then first else initial
 have hF:∀z,(rootedRunFormula 0).Eval ![z] ρ ↔ runHistory first z := by
  intro z; simpa [ρ] using rootedRunFormula_eval 0 ρ z
 have hG:∀z,(rootedRunFormula 1).Eval ![z] ρ ↔ runHistory initial z := by
  intro z; simpa [ρ] using rootedRunFormula_eval 1 ρ z
 exact history_splice (rootedRunFormula 0) (rootedRunFormula 1) ρ
  (runHistory first) (runHistory initial) hF hG codedCommandStep
  (runHistory_cons_nonempty first) (runHistory_cons_nonempty initial) n s b hf hb hb.1 hhead
end ZF207.ModelOperationalConcat
