module
public import ModelReplay2146
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalUpto_member (k n : M) : t120 (t124 n) k ↔ k<n := by
 have h := p2139 k n
 simpa [t3,t2,t0,t1,t16,literalLt_order,iff_def] using h

def boundPredicateFormula (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 1 :=
 “n. ∀k, !φ k → k<n”
lemma boundPredicateFormula_eval (φ : ArithmeticSemiformula Nat 1) (e : Nat → M) (n : M) :
 (boundPredicateFormula φ).Eval ![n] e ↔ ∀k,φ.Eval ![k] e → k<n := by
 simp [boundPredicateFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]

def boundPredicate_certificate {e : Nat → M} {P : M → Prop}
 (p : FormulaCertificate e 1 (fun v=>P (v 0))) :
 FormulaCertificate e 1 (fun v=>t18 P (t120 (t124 (v 0)))) where
 formula := boundPredicateFormula p.formula
 correct := by
   intro v
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
   rw [←hv,boundPredicateFormula_eval]
   simp only [←p.correct]
   simp [t18,t8,t0,t1,t16,literalUpto_member]
end ZF207.MM0ModelReplay
