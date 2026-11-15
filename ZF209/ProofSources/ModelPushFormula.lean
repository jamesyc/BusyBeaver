module
public import ModelPushMacro
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Successful SHIFT step; missing successor is the halt case, not an arbitrary transition. -/
def shiftFormula : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
 “t w d h u v e f. t+h≠1 ∧ u=h ∧ !unpairRightGraph v w ∧ e=d ∧ !unpairLeftGraph f w”
lemma shiftFormula_eval (t w d h u v e f:M) : shiftFormula.val.Evalb ![t,w,d,h,u,v,e,f] ↔
 modelCommandEval (.shift : Command M) ⟨t,w,d,h⟩ = some ⟨u,v,e,f⟩ := by
 have hl (z n:M) : unpairLeftGraph.val.Evalb ![z,n] ↔ z=modelUnpairLeft n := graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![n]
 have hr (z n:M) : unpairRightGraph.val.Evalb ![z,n] ↔ z=modelUnpairRight n := graphValue_spec unpairRightGraph unpairRightGraph_total z ![n]
 simp [shiftFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,numeral_eq_natCast]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,hl,hr]
 by_cases hh:t+h=1
 · simp [modelCommandEval,hh]
 · simp [modelCommandEval,hh,eq_comm]
end ZF209.ModelCommands
