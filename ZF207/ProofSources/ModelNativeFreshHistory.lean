module
public import ModelNativeFreshFetch
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def firstRunSimulation (n initial:M) (start:State M) (code:M) : Prop := runHistory initial code →
 modelListHead code=initial ∨ nativeReaches start (liftState n (modelListHead code))
noncomputable def firstRunFormula : ArithmeticSemiformula Nat 1 :=
 “code. !runFormula &1 code → ∃last, !listHeadGraph last code ∧
 (last=&1 ∨ ∃target, !liftStateGraph target &0 last ∧
 ∀root, ∀hist, (!nativeRunFormula root hist ∧ !listHeadGraph &2 hist) →
 ∃out, !nativeRunFormula root out ∧ !listHeadGraph target out)”
lemma firstRunFormula_eval (n initial:M) (start:State M) (code:M) :
 firstRunFormula.Eval ![code] (fun i=>if i=0 then n else if i=1 then initial else stateCode start) ↔
 firstRunSimulation n initial start code := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [firstRunFormula,firstRunSimulation,nativeReaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,runFormula_eval,nativeRunFormula_eval,
 ruleHead_defined.iff,liftStateGraph_eval,eq_comm]
noncomputable def firstRun_certificate (n initial:M) (start:State M) :
 FormulaCertificate (fun i=>if i=0 then n else if i=1 then initial else stateCode start) 1
 (fun v=>firstRunSimulation n initial start (v 0)) := by
 refine ⟨firstRunFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv];exact (firstRunFormula_eval n initial start (v 0)).symm
theorem fresh_history_native (hc:successBodyContract (M:=M)) (candidate:M) (s:Store M) :
 ∀code:M,firstRunSimulation (candidate+1) (commandCfgCode (candidate+1) s)
 (commandState 25 candidate 0 0 s) code := by
 apply (firstRun_certificate (candidate+1) (commandCfgCode (candidate+1) s) (commandState 25 candidate 0 0 s)).orderInduction
 intro code ih
 change firstRunSimulation _ _ _ code
 intro hr
 have hp:0<code:=pos_iff_ne_zero.mpr hr.1
 have he:code=modelListCons (modelListHead code) (modelListTail code):=(modelList_reconstruct code hp).symm
 have ht:=modelListTail_lt code hp
 rw [he] at hr ⊢
 simp only [modelListHead_cons]
 by_cases hz:modelListTail code=0
 · rw [hz] at hr
   have hstep:=(modelTrace_cons (runEdge _) (modelListHead code) 0).mp hr.2
   exact Or.inl (by simpa [runEdge] using hstep.2)
 · obtain ⟨hprev,hstep⟩ := (runHistory_cons_nonempty _ _ _ hz).mp hr
   rcases ih _ ht hprev with hfirst|hprefix
   · apply Or.inr
     change modelListHead (modelListTail code)=commandCfgCode (candidate+1) s at hfirst
     rw [hfirst] at hstep
     exact fresh_first_step hc candidate s hstep
   · exact Or.inr (nativeReaches_trans hprefix (codedStep_native hc (candidate+1) hstep))
end ZF207.NativeCommands
