module
public import ModelLeastInductionCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma literalRestrictedGraph_iff (P : M → Prop) (F : M → M) (z : M) :
 t81 (t82 F) P z ↔ ∃x,P x ∧ z=t63 x (F x) := by
 classical
 simp [t81,t19,t75,t74,t22,t25,t14,t15,t16,t2,t0,t1,t6,t82,t9,t8,t10]
 constructor
 · rintro ⟨⟨x,hx⟩,hp⟩
   refine ⟨x,?_,hx⟩
   have hx0 := p1277 x (F x)
   change t64 (t63 x (F x))=x at hx0
   simpa [hx,hx0] using hp
 · rintro ⟨x,hp,rfl⟩
   refine ⟨⟨x,rfl⟩,?_⟩
   have hx0 := p1277 x (F x)
   change t64 (t63 x (F x))=x at hx0
   simpa [hx0] using hp

def restrictedGraphFormula (p : ArithmeticSemiformula Nat 1)
 (g : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 1 :=
 ∃¹ (selectUnary 0 p ⋏ (Rew.bind (L := ℒₒᵣ) ![#1,#0] Semiterm.fvar ▹ pairedFunctionFormula g))

def literalRestrictedGraph_certificate {e : Nat → M} {P : M → Prop} {F : M → M}
 (p : FormulaCertificate e 1 (fun v => P (v 0)))
 (g : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FormulaCertificate e 1 (fun v => t81 (t82 F) P (v 0)) where
 formula := restrictedGraphFormula p.formula g.formula
 correct := by
   intro v
   rw [literalRestrictedGraph_iff]
   simp only [restrictedGraphFormula]
   simp [selectUnary_eval,Semiformula.eval_rew,Function.comp_def,←p.correct]
   have hm (w : Fin 2 → M) : (fun i => Semiterm.val w e (![#1,#0] i : ArithmeticSemiterm Nat 2)) = ![w 1,w 0] := by
     funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
   simp only [hm]
   change (∃x,P x ∧ v 0=t63 x (F x)) ↔ ∃x,P x ∧ (pairedFunctionFormula g.formula).Eval ![v 0,x] e
   have hg (y x : M) : g.formula.Eval ![y,x] e ↔ y=F x := g.correct ![x] y
   simp only [pairedFunctionFormula_eval,hg]
   simp
end ZF207.MM0ModelReplay
