module
public import ModelLiteralFunctionGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalPairFunctionsFormula (f g : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 ∃¹ ∃¹ (((Rew.bind (L:=ℒₒᵣ) ![#1,#3] Semiterm.fvar ▹ f) ⋏
          (Rew.bind (L:=ℒₒᵣ) ![#0,#3] Semiterm.fvar ▹ g)) ⋏
         (Rew.bind (L:=ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar ▹ literalPairGraph))
lemma literalPairFunctionsFormula_eval (f g : ArithmeticSemiformula Nat 2)
 (e : Nat → M) (z x : M) :
 (literalPairFunctionsFormula f g).Eval ![z,x] e ↔
 ∃u v,f.Eval ![u,x] e ∧ g.Eval ![v,x] e ∧ z=t63 u v := by
 simp [literalPairFunctionsFormula,Semiformula.eval_rew,Function.comp_def]
 have h1 (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#1,#3] i : ArithmeticSemiterm Nat 4)) = ![w 1,w 3] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
 have h2 (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#0,#3] i : ArithmeticSemiterm Nat 4)) = ![w 0,w 3] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
 have h3 (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#2,#1,#0] i : ArithmeticSemiterm Nat 4)) = ![w 2,w 1,w 0] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
 simp only [h1,h2,h3,literalPairGraph_eval]
 simp [and_assoc]

def literalPairFunctions_certificate {e : Nat → M} {F G : M → M}
 (f : FunctionGraphCertificate e 1 (fun v => F (v 0)))
 (g : FunctionGraphCertificate e 1 (fun v => G (v 0))) :
 FunctionGraphCertificate e 1 (fun v => t63 (F (v 0)) (G (v 0))) where
 formula := literalPairFunctionsFormula f.formula g.formula
 correct := by
   intro w z
   have hw : ![w 0]=w := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
   rw [←hw,literalPairFunctionsFormula_eval]
   have hf (y : M) := f.correct ![w 0] y
   have hg (y : M) := g.correct ![w 0] y
   simp only [hf,hg]
   constructor
   · rintro ⟨u,v,rfl,rfl,h⟩; exact h
   · intro h; exact ⟨_,_,rfl,rfl,h⟩
end ZF207.MM0ModelReplay
