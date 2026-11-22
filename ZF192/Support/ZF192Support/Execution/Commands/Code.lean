module
public import ZF192Support.Execution.Commands.StoreCode
public import ZF192Support.Execution.Commands.AXFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Encode the command in the literal operand order, with the given residual pointer. -/
noncomputable def commandCode : Command M → M → M
 | .shift,tail => modelCantor 0 tail
 | .mp x,tail => modelCantor 1 (modelCantor x tail)
 | .ax a x y,tail => modelCantor (a+2) (modelCantor y (modelCantor x tail))
lemma command_exists (P:Command M→Prop) : (∃c,P c) ↔ P .shift ∨ (∃x,P (.mp x)) ∨ (∃a x y,P (.ax a x y)) := by
 constructor
 · rintro ⟨c,h⟩; cases c with
   | shift => exact Or.inl h
   | mp x => exact Or.inr (Or.inl ⟨x,h⟩)
   | ax a x y => exact Or.inr (Or.inr ⟨a,x,y,h⟩)
 · rintro (h|⟨x,h⟩|⟨a,x,y,h⟩)
   · exact ⟨.shift,h⟩
   · exact ⟨.mp x,h⟩
   · exact ⟨.ax a x y,h⟩
/-- A fixed first-order formula, not classified Sigma1 because AX has only a general certificate. -/
noncomputable def commandFieldsFormula : ArithmeticSemiformula Nat 10 :=
 “pc tail t w d h u v e f.
 (!exactCantorGraph pc 0 tail ∧ !shiftFormula t w d h u v e f) ∨
 (∃x, ∃q, !exactCantorGraph q x tail ∧ !exactCantorGraph pc 1 q ∧ !mpFormula x t w d h u v e f) ∨
 (∃a, ∃x, ∃y, ∃q, ∃r, !exactCantorGraph q x tail ∧ !exactCantorGraph r y q ∧
 !exactCantorGraph pc (a+2) r ∧ !fixedAXFormula a x y t w d h u v e f)”
lemma commandFieldsFormula_eval (ρ:Nat→M) (pc tail t w d h u v e f:M) :
 commandFieldsFormula.Eval ![pc,tail,t,w,d,h,u,v,e,f] ρ ↔
 ∃c, pc=commandCode c tail ∧ modelCommandEval c ⟨t,w,d,h⟩=some ⟨u,v,e,f⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 rw [command_exists]
 simp [commandFieldsFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,hc,shiftFormula_eval,mpFormula_eval,fixedAXFormula_eval,commandCode]
end ZF192Support.ModelCommands
