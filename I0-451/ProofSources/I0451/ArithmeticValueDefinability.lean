module
public import I0451.ArithmeticAxioms
public import I0451.ArithmeticExpressionCode

/-! Definability of arithmetic register updates, including the emitted
formula-building operations. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmeticCompare_defined {k : Nat} (left right yes no : (Fin k → V) → V)
    (hl : 𝚺ᴬ₁.DefinableFunction (V := V) left)
    (hr : 𝚺ᴬ₁.DefinableFunction (V := V) right)
    (hy : 𝚺ᴬ₁.DefinableFunction (V := V) yes)
    (hn : 𝚺ᴬ₁.DefinableFunction (V := V) no) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => if left v = right v then yes v else no v) := by
  obtain ⟨l, leftGraph⟩ := hl
  obtain ⟨r, rightGraph⟩ := hr
  obtain ⟨y, yesGraph⟩ := hy
  obtain ⟨n, noGraph⟩ := hn
  let formula : 𝚺ᴬ₁.Semiformula V (k + 1) := .mkSigma
    “out. ∃ a b, !(l.val) a ⋯ ∧ !(r.val) b ⋯ ∧ ((a = b ∧ !(y.val) out ⋯) ∨ (a ≠ b ∧ !(n.val) out ⋯))”
  refine ⟨formula, fun v => ?_⟩
  have evaluation :
      formula.val.Eval v id ↔ ∃ a b : V, a = left (v ·.succ) ∧ b = right (v ·.succ) ∧
        ((a = b ∧ v 0 = yes (v ·.succ)) ∨ (a ≠ b ∧ v 0 = no (v ·.succ))) := by
    simp [formula, leftGraph.iff, rightGraph.iff, yesGraph.iff, noGraph.iff,
      BinderNotation.finSuccItr]
  rw [evaluation]
  by_cases eq : left (v ·.succ) = right (v ·.succ) <;> simp [eq]

theorem counterExpr_modelEval_defined {k : Nat} (expr : CounterExpr) (s : (Fin k → V) → Fin 9 → V)
    (defined : ∀ r : Fin 9, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v r)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => expr.modelEval (s v)) := by
  have graph : 𝚺ᴬ₁.DefinableFunction (V := V) (fun input : Fin 9 → V => expr.modelEval input) :=
    expr.graph_defines.to_definable
  exact Bounding.HierarchySymbol.DefinableFunction.substitution (f := fun i v => s v i) graph defined

theorem modelAxiom_field_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (r : Fin 9)
    (defined : ∀ j : Fin 9, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelAxiomResult (s v) r) := by
  have before (v : Fin k → V) : (symbolicInput false).modelEval (s v) = s v := by
    funext i
    simp [symbolicInput, SymbolicRegisters.modelEval, CounterExpr.modelEval]
  have exactValue (v : Fin k → V) :
      (axiomPost (symbolicInput false) r).modelEval (s v) = modelAxiomResult (s v) r := by
    have eq := modelEval_axiomPost (symbolicInput false) (s v)
    rw [before v] at eq
    exact congrFun eq r
  simpa only [exactValue] using counterExpr_modelEval_defined (axiomPost (symbolicInput false) r) s defined

end I0451.Arithmetization
