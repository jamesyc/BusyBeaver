module
public import ModelReplayCertificateHelpers
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def FormulaCertificate.reindexParameters {e : Nat → M} {n} {P : (Fin n → M) → Prop}
 (p : FormulaCertificate e n P) (e' : Nat → M) (σ : Nat → Nat)
 (h : ∀i,e' (σ i)=e i) : FormulaCertificate e' n P where
 formula := Rew.bind (L := ℒₒᵣ) Semiterm.bvar (fun i => Semiterm.fvar (σ i)) ▹ p.formula
 correct := by
   intro v
   rw [Semiformula.eval_rew]
   simpa [Function.comp_def,h] using p.correct v

namespace FunctionGraphCertificate

def prependParameter {e : Nat → M} {n} {F : (Fin n → M) → M}
 (g : FunctionGraphCertificate e n F) (a : M) :
 FunctionGraphCertificate (fun i => Nat.casesOn i a e) n F where
 formula := Rew.bind (L := ℒₒᵣ) Semiterm.bvar (fun i => Semiterm.fvar (i+1)) ▹ g.formula
 correct := by
   intro v y
   rw [Semiformula.eval_rew]
   simpa [Function.comp_def] using g.correct v y

def equal {e : Nat → M} {n} {F G : (Fin n → M) → M}
 (f : FunctionGraphCertificate e n F) (g : FunctionGraphCertificate e n G) :
 FormulaCertificate e n (fun v => F v=G v) where
 formula := ∃¹ (f.formula ⋏ g.formula)
 correct := by
   intro v
   change F v=G v ↔ ∃y,f.formula.Eval (y :> v) e ∧ g.formula.Eval (y :> v) e
   simp only [f.correct,g.correct]
   constructor
   · intro h; exact ⟨F v,rfl,h⟩
   · rintro ⟨y,hf,hg⟩; exact hf.symm.trans hg
end FunctionGraphCertificate

/-- A single fixed proposition can be coded by one parameter. This supplies
no syntax for an arbitrary variable-indexed predicate. -/
noncomputable def truthParameter (P : Prop) : M := by
 classical
 exact if P then 1 else 0

def constantCertificate (e : Nat → M) (P : Prop) (n : Nat) :
 FormulaCertificate (M := M) (fun i : Nat => Nat.casesOn i (truthParameter (M:=M) P) e) n (fun _ => P) where
 formula := “&0=1”
 correct := by
   intro v
   classical
   change P ↔ truthParameter (M:=M) P=1
   by_cases h : P
   · simp [truthParameter,h]
   · simp [truthParameter,h]
end ZF209.MM0ModelPeano
