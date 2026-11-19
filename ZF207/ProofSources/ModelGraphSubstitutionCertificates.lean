module
public import ModelDescriptionCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano

/-- Actual arithmetic graph syntax. The output is bound variable zero;
inputs follow it. A certificate is supplied, never inferred for arbitrary F. -/
structure FunctionGraphCertificate {M : Type*} [ORingStructure M]
 (e : Nat → M) (n : Nat) (F : (Fin n → M) → M) where
 formula : ArithmeticSemiformula Nat (n+1)
 correct : ∀ v y, formula.Eval (y :> v) e ↔ y=F v

/-- Replace the first argument of a predicate by a graph-defined value, while
retaining all remaining arguments and the same free-parameter assignment. -/
def graphSubstitutionFormula {n}
 (graph predicate : ArithmeticSemiformula Nat (n+1)) : ArithmeticSemiformula Nat n :=
 ∃¹ (graph ⋏ predicate)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

namespace FunctionGraphCertificate

def substitute {e : Nat → M} {n} {F : (Fin n → M) → M}
 (g : FunctionGraphCertificate e n F)
 {P : (Fin (n+1) → M) → Prop} (p : FormulaCertificate e (n+1) P) :
 FormulaCertificate e n (fun v => P (F v :> v)) where
 formula := graphSubstitutionFormula g.formula p.formula
 correct := by
   intro v
   change P (F v :> v) ↔ ∃ y, g.formula.Eval (y :> v) e ∧ p.formula.Eval (y :> v) e
   simp only [g.correct, ←p.correct]
   constructor
   · intro h; exact ⟨F v,rfl,h⟩
   · rintro ⟨y,rfl,h⟩; exact h

/-- The description construction produces actual graph syntax for its
unique-or-zero function, with no uniqueness assumption on the predicate. -/
def ofDescription {e : Nat → M} {n}
 {P : (Fin (n+1) → M) → Prop} (p : FormulaCertificate e (n+1) P) :
 FunctionGraphCertificate e n (fun v => the (fun y => P (y :> v))) where
 formula := descriptionGraph p.formula
 correct := by
   intro v y
   rw [descriptionGraph_eval (M := M)]
   simp only [←p.correct]
   exact the_graph (fun x => P (x :> v)) y

end FunctionGraphCertificate
end ZF207.MM0ModelPeano
