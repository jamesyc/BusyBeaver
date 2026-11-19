module
public import ModelBoundedGraphCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
open ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def pairedFunctionFormula (g : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 ∃¹ ((Rew.bind (L := ℒₒᵣ) ![#0,#2] Semiterm.fvar ▹ g) ⋏
     (Rew.bind (L := ℒₒᵣ) ![#1,#2,#0] Semiterm.fvar ▹ literalPairGraph))

lemma pairedFunctionFormula_eval (g : ArithmeticSemiformula Nat 2)
 (e : Nat → M) (z x : M) :
 (pairedFunctionFormula g).Eval ![z,x] e ↔
 ∃y,g.Eval ![y,x] e ∧ z=t63 x y := by
 simp [pairedFunctionFormula,Semiformula.eval_rew,Function.comp_def]
 have hm2 (w : Fin 3 → M) : (fun i => Semiterm.val w e (![#0,#2] i : ArithmeticSemiterm Nat 3)) = ![w 0,w 2] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
 have hm3 (w : Fin 3 → M) : (fun i => Semiterm.val w e (![#1,#2,#0] i : ArithmeticSemiterm Nat 3)) = ![w 1,w 2,w 0] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
 simp only [hm2,hm3]
 change (∃y,g.Eval ![y,x] e ∧ literalPairGraph.Eval ![z,x,y] e) ↔ _
 simp only [literalPairGraph_eval]

def FunctionGraphCertificate.pairWithArgument {e : Nat → M} {F : M → M}
 (g : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FunctionGraphCertificate e 1 (fun v => t63 (v 0) (F (v 0))) where
 formula := pairedFunctionFormula g.formula
 correct := by
   intro v z
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
   rw [←hv]
   rw [pairedFunctionFormula_eval]
   have hg (y : M) : g.formula.Eval ![y,v 0] e ↔ y=F (v 0) := g.correct ![v 0] y
   simp only [hg]
   constructor
   · rintro ⟨y,rfl,h⟩; exact h
   · intro h; exact ⟨_,rfl,h⟩
end ZF207.MM0ModelPeano
