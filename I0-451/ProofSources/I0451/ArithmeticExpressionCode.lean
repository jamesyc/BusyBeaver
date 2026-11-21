module
public import I0451.ArithmeticSymbolic

/-! Compile the shared counter expressions to first-order arithmetic
graphs. The output is the first slot, followed by the nine inputs. -/
@[expose] public section
namespace I0451.Runtime

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Arithmetization

def CounterExpr.graph : CounterExpr → 𝚺ᴬ₁.Semisentence 10
  | .input i => .mkSigma “out. out = !!#i.succ”
  | .number n => .mkSigma “out. out = ↑(n)”
  | .add left right =>
    let a := left.graph
    let b := right.graph
    .mkSigma “out. ∃ x y, !a x ⋯ ∧ !b y ⋯ ∧ out = x + y”
  | .pair left right =>
    let a := left.graph
    let b := right.graph
    .mkSigma “out. ∃ x y, !a x ⋯ ∧ !b y ⋯ ∧ !cantorDef out x y”
  | .first operand =>
    let a := operand.graph
    .mkSigma “out. ∃ x, !a x ⋯ ∧ !cantorLeftDef out x”
  | .second operand =>
    let a := operand.graph
    .mkSigma “out. ∃ x, !a x ⋯ ∧ !cantorRightDef out x”
  | .scaled operand =>
    let a := operand.graph
    .mkSigma “out. ∃ x, !a x ⋯ ∧ out = 4 * x”
  | .ifEqual left right yes no =>
    let a := left.graph
    let b := right.graph
    let y := yes.graph
    let n := no.graph
    .mkSigma “out. ∃ p q, !a p ⋯ ∧ !b q ⋯ ∧ ((p = q ∧ !y out ⋯) ∨ (p ≠ q ∧ !n out ⋯))”

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem CounterExpr.graph_eval (expr : CounterExpr) (v : Fin 10 → V) :
    expr.graph.val.Evalb v ↔ v 0 = expr.modelEval (v ·.succ) := by
  induction expr generalizing v with
  | input i => simp [graph, modelEval]
  | number n => simp [graph, modelEval, numeral_eq_natCast]
  | add a b ha hb => simp [graph, modelEval, ha, hb, BinderNotation.finSuccItr]
  | pair a b ha hb => simp [graph, modelEval, ha, hb, cantor_defined.iff, BinderNotation.finSuccItr]
  | first a ih => simp [graph, modelEval, ih, cantorLeft_eval, BinderNotation.finSuccItr]
  | second a ih => simp [graph, modelEval, ih, cantorRight_eval, BinderNotation.finSuccItr]
  | scaled a ih => simp [graph, modelEval, ih, BinderNotation.finSuccItr]
  | ifEqual a b yes no ha hb hy hn =>
    by_cases equal : a.modelEval (v ·.succ) = b.modelEval (v ·.succ) <;>
      simp [graph, modelEval, ha, hb, hy, hn, BinderNotation.finSuccItr, equal]

theorem CounterExpr.graph_defines (expr : CounterExpr) :
    𝚺ᴬ₁.DefinedFunction (V := V) (fun input : Fin 9 → V => expr.modelEval input) expr.graph :=
  .mk (expr.graph_eval)

/-- Use a smaller arity by specifying which input supplies each slot. -/
def CounterExpr.graphOn {n : Nat} (expr : CounterExpr) (slots : Fin 10 → Fin n) :
    𝚺ᴬ₁.Semisentence n :=
  expr.graph.rew (Rew.subst (fun i => #(slots i)))

theorem CounterExpr.graphOn_eval {n : Nat} (expr : CounterExpr) (slots : Fin 10 → Fin n) (v : Fin n → V) :
    (expr.graphOn slots).val.Evalb v ↔ v (slots 0) = expr.modelEval (fun i => v (slots i.succ)) := by
  simpa only [graphOn, Bounding.HierarchySymbol.Semiformula.val_rew, Semiformula.eval_substs,
    Semiterm.val_bvar, Function.comp_def] using expr.graph_eval (fun i => v (slots i))

end I0451.Runtime
