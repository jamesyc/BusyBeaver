module
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Explicit syntax witness at a common parameter assignment. No arbitrary
semantic predicate is presumed arithmetically definable. -/
structure FormulaCertificate (e : Nat → M) (n : Nat) (P : (Fin n → M) → Prop) where
 formula : ArithmeticSemiformula Nat n
 correct : ∀ v, P v ↔ formula.Eval v e

namespace FormulaCertificate
variable {e : Nat → M} {n : Nat} {P Q : (Fin n → M) → Prop}

def imp (a : FormulaCertificate e n P) (b : FormulaCertificate e n Q) :
 FormulaCertificate e n (fun v => P v → Q v) where
 formula := a.formula 🡒 b.formula
 correct := by intro v; simp [←a.correct,←b.correct]

/-- Apply PA induction using the formula and its parameter assignment. -/
theorem induction {P : (Fin 1 → M) → Prop} (a : FormulaCertificate e 1 P)
 (hz : P ![0]) (hs : ∀ x, P ![x] → P ![x+1]) : ∀ x, P ![x] := by
 have : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
   models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 exact InductionScheme.succ_induction (C := Set.univ) (P := fun x => P ![x])
   ⟨e, a.formula, True.intro, fun x => a.correct ![x]⟩ hz hs

end FormulaCertificate
end ZF192Support.MM0ModelPeano
