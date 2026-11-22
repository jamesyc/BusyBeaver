module
public import ZF192Support.Execution.Commands.Program.Retarget
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def reverseCommandStep (remaining accumulator:M) : M :=
 if remaining=0 then accumulator else retargetCommand (modelPredecessor remaining) accumulator+1
lemma reverseCommandStep_zero (accumulator:M) : reverseCommandStep 0 accumulator=accumulator := by
 simp [reverseCommandStep]
lemma reverseCommandStep_cons (c:Command M) (tail accumulator:M) :
 reverseCommandStep (commandCode c tail+1) accumulator=commandCode c accumulator+1 := by
 simp [reverseCommandStep,modelPredecessor_succ,retargetCommand_code]
def reverseCommandStepGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z remaining accumulator. (remaining=0 ∧ z=accumulator) ∨
 (remaining≠0 ∧ ∃p, ∃r, !predecessorGraph p remaining ∧ !retargetGraph r p accumulator ∧ z=r+1)”
lemma reverseCommandStepGraph_eval (z remaining accumulator:M) :
 reverseCommandStepGraph.val.Evalb ![z,remaining,accumulator] ↔ z=reverseCommandStep remaining accumulator := by
 have hp (z n:M) : predecessorGraph.val.Evalb ![z,n] ↔ z=modelPredecessor n :=
  graphValue_spec predecessorGraph predecessorGraph_total z ![n]
 simp [reverseCommandStepGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,hp,retarget_defined.iff]
 by_cases h:remaining=0 <;> simp [reverseCommandStep,h]
lemma reverseCommandStep_defined : 𝚺ᴬ₁.DefinedFunction₂ (reverseCommandStep (M:=M)) reverseCommandStepGraph := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_three v]; exact reverseCommandStepGraph_eval _ _ _)
instance reverseCommandStep_definable : 𝚺ᴬ₁-Function₂ (reverseCommandStep (M:=M)) :=
 reverseCommandStep_defined.to_definable
end ZF192Support.ModelCommands
