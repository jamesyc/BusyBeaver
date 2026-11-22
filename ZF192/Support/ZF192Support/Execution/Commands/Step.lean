module
public import ZF192Support.Execution.Commands.Code
public import ZF192Support.Coding.Histories.General
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def commandCfgCode (pointer:M) (s:Store M) : M := modelCantor pointer (storeCode s)
/-- Successful residual command step. Positive residual pointer is commandCode+1.
Pointer zero is exhaustion, not an execution halt; SHIFT halting is separate. -/
def codedCommandStep (before after:M) : Prop := ∃ (c:Command M) (tail:M) (s s':Store M),
 before=commandCfgCode (commandCode c tail+1) s ∧ after=commandCfgCode tail s' ∧
 modelCommandEval c s=some s'
noncomputable def commandStepFormula : ArithmeticSemiformula Nat 2 :=
 “before after. ∃pc, ∃tail, ∃old, ∃new,
 !exactCantorGraph before (pc+1) old ∧ !exactCantorGraph after tail new ∧
 ∃t, ∃w, ∃d, ∃h, ∃u, ∃v, ∃e, ∃f,
 !storeGraph old t w d h ∧ !storeGraph new u v e f ∧
 !commandFieldsFormula pc tail t w d h u v e f”
lemma commandStepFormula_eval (ρ:Nat→M) (before after:M) :
 commandStepFormula.Eval ![before,after] ρ ↔ codedCommandStep before after := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp only [commandStepFormula]
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
 Empty.eq_elim,hc,storeGraph_eval,commandFieldsFormula_eval]
 constructor
 · rintro ⟨tail,t,w,d,h,u,v,e,f,c,hb,ha,he⟩
   exact ⟨c,tail,⟨t,w,d,h⟩,⟨u,v,e,f⟩,hb,ha,he⟩
 · rintro ⟨c,tail,⟨t,w,d,h⟩,⟨u,v,e,f⟩,hb,ha,he⟩
   exact ⟨tail,t,w,d,h,u,v,e,f,c,hb,ha,he⟩
lemma codedCommandStep_of_eval (c:Command M) (tail:M) (s s':Store M)
 (h:modelCommandEval c s=some s') :
 codedCommandStep (commandCfgCode (commandCode c tail+1) s) (commandCfgCode tail s') :=
 ⟨c,tail,s,s',rfl,rfl,h⟩
end ZF192Support.ModelCommands
