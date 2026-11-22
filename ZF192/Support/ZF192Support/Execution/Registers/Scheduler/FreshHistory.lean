module
public import ZF192Support.Execution.Registers.Scheduler.FreshFetch
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano ModelOperationalConcat
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
 simp [firstRunFormula,firstRunSimulation,nativeReaches,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,runFormula_eval,nativeRunFormula_eval,
 ruleHead_defined.iff,liftStateGraph_eval,eq_comm]
theorem fresh_history_native (hc : successBodyContract (M := M)) (candidate : M) (s : Store M) :
    ∀ code : M, firstRunSimulation (candidate + 1) (commandCfgCode (candidate + 1) s)
      (commandState 25 candidate 0 0 s) code := by
  let n := candidate + 1
  let initial := commandCfgCode n s
  let start := commandState 25 candidate 0 0 s
  exact ModelScheduler.rooted_induction codedCommandStep initial firstRunFormula
    (fun i => if i = 0 then n else if i = 1 then initial else stateCode start)
    (fun last => last = initial ∨ nativeReaches start (liftState n last))
    (firstRunFormula_eval n initial start) (Or.inl rfl) (by
      intro before after hs hr
      right
      rcases hr with rfl | prefixRun
      · exact fresh_first_step hc candidate s hs
      · exact nativeReaches_trans prefixRun (codedStep_native hc n hs))
end ZF192Support.NativeCommands
