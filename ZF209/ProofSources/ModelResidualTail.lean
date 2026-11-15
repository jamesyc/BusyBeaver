module
public import ModelCommandParse
public import ExactTailIterationModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def residualTail (n:M) : M := if n=0 then 0 else (parseCommand (modelPredecessor n)).2
lemma residualTail_zero : residualTail (0:M)=0 := by simp [residualTail]
lemma residualTail_code (c:Command M) (tail:M) : residualTail (commandCode c tail+1)=tail := by
 simp [residualTail,modelPredecessor_succ,parseCommand_code]
lemma residualTail_lt (n:M) (hn:0<n) : residualTail n<n := by
 rw [residualTail,if_neg (ne_of_gt hn)]
 exact lt_of_le_of_lt (parseCommand_next_le _) (by
  have h:=modelPredecessor_of_pos n hn
  simpa only [h] using (show modelPredecessor n<modelPredecessor n+1 by simp))
def residualTailGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “z n. (n=0 ∧ z=0) ∨ (n≠0 ∧ ∃p, ∃a, ∃b,
 !predecessorGraph p n ∧ !unpairLeftGraph a p ∧ !unpairRightGraph b p ∧
 ((a=0 ∧ z=b) ∨ (a=1 ∧ !unpairRightGraph z b) ∨
 (a≠0 ∧ a≠1 ∧ ∃r, !unpairRightGraph r b ∧ !unpairRightGraph z r)))”
lemma residualTailGraph_eval (z n:M) : residualTailGraph.val.Evalb ![z,n] ↔ z=residualTail n := by
 have hp (z n:M) : predecessorGraph.val.Evalb ![z,n] ↔ z=modelPredecessor n := predecessorGraph_value z n
 have hl (z n:M) : unpairLeftGraph.val.Evalb ![z,n] ↔ z=modelUnpairLeft n := graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![n]
 have hr (z n:M) : unpairRightGraph.val.Evalb ![z,n] ↔ z=modelUnpairRight n := graphValue_spec unpairRightGraph unpairRightGraph_total z ![n]
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [residualTailGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,hp,hl,hr]
 by_cases hn:n=0
 · simp [residualTail,hn]
 · by_cases h0:modelUnpairLeft (modelPredecessor n)=0
   · simp [residualTail,hn,parseCommand,h0]
   · by_cases h1:modelUnpairLeft (modelPredecessor n)=1
     · simp [residualTail,hn,parseCommand,h0,h1]
     · simp [residualTail,hn,parseCommand,h0,h1]
lemma residualTail_defined : 𝚺ᴬ₁.DefinedFunction₁ (residualTail (M:=M)) residualTailGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun j=>?_) i; exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact residualTailGraph_eval _ _)
instance residualTail_definable : 𝚺ᴬ₁-Function₁ (residualTail (M:=M)) := residualTail_defined.to_definable
end ZF209.ModelCommands
