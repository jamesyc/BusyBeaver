module
public import ZF192Support.Execution.Commands.Semantics
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Parameter X, input T,W,D,H, then output T,W,D,H. Successful MP always returns.
This is one command on arbitrary model stores, not a nonstandard sequence compiler. -/
def mpFormula : 𝚺ᴬ₁.Semisentence 9 := .mkSigma
 “x t w d h u v e f. ∃ p, !exactCantorGraph p t (d+x) ∧ e=d+x ∧ f=0 ∧
 ((4*p=h ∧ u=d+x ∧ !exactCantorGraph v 0 w) ∨ (4*p≠h ∧ u=0 ∧ v=w))”
lemma mpFormula_eval (x t w d h u v e f:M) :
 mpFormula.val.Evalb ![x,t,w,d,h,u,v,e,f] ↔
 modelCommandEval (.mp x) ⟨t,w,d,h⟩ = some ⟨u,v,e,f⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp only [mpFormula,Semiformula.eval_rew]
 simp [Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,hc,numeral_eq_natCast]

 change (e=d+x ∧ f=0 ∧ ((4*modelCantor t (d+x)=h ∧ u=d+x ∧ v=modelCantor 0 w) ∨
   (4*modelCantor t (d+x)≠h ∧ u=0 ∧ v=w))) ↔ _
 by_cases hh : 4*modelCantor t (d+x)=h
 · simp [modelCommandEval,modelImp_value,hh,eq_comm,and_comm,and_left_comm,and_assoc]
 · simp [modelCommandEval,modelImp_value,hh,eq_comm,and_comm,and_left_comm,and_assoc]
end ZF192Support.ModelCommands
