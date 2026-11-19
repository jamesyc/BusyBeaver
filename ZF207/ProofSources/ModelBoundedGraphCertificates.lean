module
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def boundedGraphImageFormula (g : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 1 :=
 ∃¹ ∀¹ ((“∃q,(#1+1)+#0=#3”) 🡒
   ∃¹ ((Rew.bind (L := ℒₒᵣ) ![#0,#1] Semiterm.fvar ▹ g) ⋏ “∃q,(#1+1)+#0=#3”))

def FunctionGraphCertificate.boundedImage {e : Nat → M} {F : M → M}
 (g : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FormulaCertificate e 1 (fun v => ∃b,∀x,(∃q,(x+1)+q=v 0) → ∃q,(F x+1)+q=b) where
 formula := boundedGraphImageFormula g.formula
 correct := by
   intro v
   simp [boundedGraphImageFormula,Semiformula.eval_rew,Function.comp_def]
   have hmap (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#0,#1] i : ArithmeticSemiterm Nat 4)) = ![w 0,w 1] := by
     funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
   simp only [hmap]
   change (∃b,∀x q,(x+1)+q=v 0 → ∃q,(F x+1)+q=b) ↔
     ∃b,∀x q,(x+1)+q=v 0 → ∃z,g.formula.Eval ![z,x] e ∧ ∃q,(z+1)+q=b
   have hg (z x : M) : g.formula.Eval ![z,x] e ↔ z=F x := g.correct ![x] z
   simp only [hg]
   constructor
   · rintro ⟨b,hb⟩; refine ⟨b,?_⟩
     intro x q h; exact ⟨F x,rfl,hb x q h⟩
   · rintro ⟨b,hb⟩; refine ⟨b,?_⟩
     intro x q h; obtain ⟨z,rfl,hz⟩ := hb x q h; exact hz
end ZF207.MM0ModelPeano
