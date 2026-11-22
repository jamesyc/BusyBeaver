module
public import ZF192Support.Execution.Commands.Program.RebaseHistory
public import ZF192Support.Coding.Histories.Map
public import ZF192Support.Execution.Commands.Program.DecomposeHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Rebase an actual arbitrary model-sized rooted command run, preserving every store
and transition. No external List map substitutes for the internal code construction. -/
lemma rebase_run (initial code tail:M) (h:runHistory initial code) :
 runHistory (rebaseCfg initial tail) (rebaseHistory code tail) := by
 let ρ:Nat→M := fun i=>if i=0 then initial else if i=1 then rebaseCfg initial tail else tail
 have hF:∀z,(rootedRunFormula 0).Eval ![z] ρ ↔ runHistory initial z := by
  intro z; simpa [ρ] using rootedRunFormula_eval 0 ρ z
 have hG:∀z,(rootedRunFormula 1).Eval ![z] ρ ↔ runHistory (rebaseCfg initial tail) z := by
  intro z; simpa [ρ] using rootedRunFormula_eval 1 ρ z
 apply history_map (rootedRunFormula 0) (rootedRunFormula 1) rebaseCfgGraph
  rebaseCfg rebaseCfg_defined ρ (runHistory initial) (runHistory (rebaseCfg initial tail))
  hF hG codedCommandStep codedCommandStep tail (by simp [ρ])
  (by intro hz; exact hz.1 rfl) ?_ (runHistory_cons_nonempty initial)
  (runHistory_cons_nonempty (rebaseCfg initial tail)) (fun a b hs=>rebaseCfg_step tail hs) code h
 intro a ha
 have he:a=initial := by
  have hr:=(modelTrace_cons (runEdge initial) a 0).mp ha.2
  simpa [runEdge, ZF192Support.ModelScheduler.rootedEdge] using hr.2
 subst a
 exact runHistory_singleton _
lemma rebase_run_cfg (pc tail:M) (s:Store M) (code:M)
 (h:runHistory (commandCfgCode pc s) code) :
 runHistory (commandCfgCode (programAppend pc tail) s) (rebaseHistory code tail) := by
 simpa only [rebaseCfg_cfg] using rebase_run (commandCfgCode pc s) code tail h
/-- The exact splice contract needed by compiler composition, including early halt. -/
lemma rebase_run_result (pc tail:M) (s result:Store M) (code:M)
 (h:runHistory (commandCfgCode pc s) code)
 (ho:haltAt (modelListHead code) ∨ modelListHead code=commandCfgCode 0 result) :
 runHistory (commandCfgCode (programAppend pc tail) s) (rebaseHistory code tail) ∧
 (haltAt (modelListHead (rebaseHistory code tail)) ∨
 modelListHead (rebaseHistory code tail)=commandCfgCode tail result) := by
 refine ⟨rebase_run_cfg pc tail s code h,?_⟩
 rcases ho with hh|he
 · exact Or.inl (rebaseHistory_halt tail h.1 hh)
 · exact Or.inr (rebaseHistory_exhausted tail result h.1 he)
end ZF192Support.ModelCommands
