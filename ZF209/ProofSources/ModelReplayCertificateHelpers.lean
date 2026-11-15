module
public import ModelGraphSubstitutionCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

namespace FormulaCertificate
/-- Insert one actual parameter, reindexing all existing free variables. -/
def prependParameter {e : Nat → M} {n} {P : (Fin n → M) → Prop}
 (p : FormulaCertificate e n P) (a : M) :
 FormulaCertificate (fun i => Nat.casesOn i a e) n P where
 formula := Rew.bind (L := ℒₒᵣ) Semiterm.bvar (fun i => Semiterm.fvar (i+1)) ▹ p.formula
 correct := by
   intro v
   rw [Semiformula.eval_rew]
   simpa [Function.comp_def] using p.correct v

/-- Literal existential-addition definition of a bounded strict comparison.
Uses actual supplied predicate syntax, not a truth-value oracle. -/
def boundedAll {e : Nat → M} {P : M → Prop}
 (p : FormulaCertificate e 1 (fun v => P (v 0))) :
 FormulaCertificate e 1 (fun v => ∀y,(∃q,(y+1)+q=v 0) → P y) where
 formula := ∀¹ (“∃ q, (#1+1)+q=#2” 🡒
   (Rew.bind (L := ℒₒᵣ) ![#0] Semiterm.fvar ▹ p.formula))
 correct := by
   intro v
   simp [Semiformula.eval_rew,Function.comp_def]
   constructor
   · intro h y q hy
     exact (p.correct (fun _ => y)).mp (h y q hy)
   · intro h y q hy
     exact (p.correct (fun _ => y)).mpr (h y q hy)
end FormulaCertificate
end ZF209.MM0ModelPeano
