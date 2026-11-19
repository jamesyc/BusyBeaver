module
public import ModelPeanoBasis
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Explicit syntax witness at a common parameter assignment. No arbitrary
semantic predicate is presumed arithmetically definable. -/
structure FormulaCertificate (e : Nat → M) (n : Nat) (P : (Fin n → M) → Prop) where
 formula : ArithmeticSemiformula Nat n
 correct : ∀ v, P v ↔ formula.Eval v e

namespace FormulaCertificate
variable {e : Nat → M} {n : Nat} {P Q : (Fin n → M) → Prop}

def neg (a : FormulaCertificate e n P) : FormulaCertificate e n (fun v => ¬P v) where
 formula := ∼a.formula
 correct := by intro v; simp [←a.correct]

def imp (a : FormulaCertificate e n P) (b : FormulaCertificate e n Q) :
 FormulaCertificate e n (fun v => P v → Q v) where
 formula := a.formula 🡒 b.formula
 correct := by intro v; simp [←a.correct,←b.correct]

def conj (a : FormulaCertificate e n P) (b : FormulaCertificate e n Q) :
 FormulaCertificate e n (fun v => P v ∧ Q v) where
 formula := a.formula ⋏ b.formula
 correct := by intro v; simp [←a.correct,←b.correct]

def all {P : (Fin (n+1) → M) → Prop} (a : FormulaCertificate e (n+1) P) :
 FormulaCertificate e n (fun v => ∀x,P (x :> v)) where
 formula := ∀¹ a.formula
 correct := by intro v; simp [←a.correct]

def ex {P : (Fin (n+1) → M) → Prop} (a : FormulaCertificate e (n+1) P) :
 FormulaCertificate e n (fun v => ∃x,P (x :> v)) where
 formula := ∃¹ a.formula
 correct := by intro v; simp [←a.correct]

/-- Adapter for the MM0 induction axiom, using the actual supplied syntax.
This is not an unrestricted induction principle for semantic predicates. -/
theorem induction {P : (Fin 1 → M) → Prop} (a : FormulaCertificate e 1 P)
 (hz : P ![0]) (hs : ∀x,P ![x] → P ![x+1]) : ∀x,P ![x] := by
 have h := peano5_formula a.formula e
 have h0 : sb 0 (fun x => a.formula.Eval ![x] e) :=
   (sb_iff (M := M) 0 (fun x => a.formula.Eval ![x] e)).mpr ((a.correct _).mp hz)
 have hstep : ∀x,a.formula.Eval ![x] e → sb (x+1) (fun x => a.formula.Eval ![x] e) := by
   intro x hx
   apply (sb_iff (M := M) (x+1) (fun x => a.formula.Eval ![x] e)).mpr
   exact (a.correct _).mp (hs x ((a.correct _).mpr hx))
 intro x
 exact (a.correct _).mpr (h h0 hstep x)
end FormulaCertificate
end ZF207.MM0ModelPeano
