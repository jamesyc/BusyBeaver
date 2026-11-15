module
public import ModelGraphEqualityCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
namespace FunctionGraphCertificate

def compose {e : Nat → M} {F G : M → M}
 (f : FunctionGraphCertificate e 1 (fun v => F (v 0)))
 (g : FunctionGraphCertificate e 1 (fun v => G (v 0))) :
 FunctionGraphCertificate e 1 (fun v => F (G (v 0))) where
 formula := ∃¹ ((Rew.bind (L:=ℒₒᵣ) ![#0,#2] Semiterm.fvar ▹ g.formula) ⋏
   (Rew.bind (L:=ℒₒᵣ) ![#1,#0] Semiterm.fvar ▹ f.formula))
 correct := by
   intro v z
   have hg (y : M) : g.formula.Eval ![y,v 0] e ↔ y=G (v 0) := g.correct ![v 0] y
   have hf (y : M) : f.formula.Eval ![z,y] e ↔ z=F y := f.correct ![y] z
   simp only [Semiformula.eval_ex]
   simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
   have hv (x : M) : (fun _ : Fin 1 => x) = ![x] := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
   simp only [hv]
   change (∃y,g.formula.Eval ![y,v 0] e ∧ f.formula.Eval ![z,y] e) ↔ _
   simp only [hg,hf]
   constructor
   · rintro ⟨y,rfl,h⟩; exact h
   · intro h; exact ⟨G (v 0),rfl,h⟩

def precomposeSucc {e : Nat → M} {F : M → M}
 (f : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FunctionGraphCertificate e 1 (fun v => F (v 0+1)) := by
 let g : FunctionGraphCertificate e 1 (fun v => v 0+1) := {
   formula := “y x. y=x+1”
   correct := by intro v y; rfl
 }
 exact f.compose (G := fun x => x+1) g

def ifThenElse {e : Nat → M} {P : M → Prop} {F G : M → M}
 (p : FormulaCertificate e 1 (fun v => P (v 0)))
 (f : FunctionGraphCertificate e 1 (fun v => F (v 0)))
 (g : FunctionGraphCertificate e 1 (fun v => G (v 0))) :
 FunctionGraphCertificate e 1 (fun v => @ite M (P (v 0)) (Classical.propDecidable _) (F (v 0)) (G (v 0))) where
 formula := (((Rew.bind (L:=ℒₒᵣ) ![#1] Semiterm.fvar ▹ p.formula) ⋏ f.formula) ⋎
   ((∼(Rew.bind (L:=ℒₒᵣ) ![#1] Semiterm.fvar ▹ p.formula)) ⋏ g.formula))
 correct := by
   intro v z
   classical
   have hp : (Rew.bind (L:=ℒₒᵣ) ![#1] Semiterm.fvar ▹ p.formula).Eval (z :> v) e ↔ P (v 0) := by
     rw [Semiformula.eval_rew]
     have hv : (fun _ : Fin 1 => v 0) = v := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
     simpa [Function.comp_def,hv] using (p.correct v).symm
   simp [hp,f.correct,g.correct]
   by_cases h : P (v 0) <;> simp [h]
end FunctionGraphCertificate
end ZF209.MM0ModelPeano
