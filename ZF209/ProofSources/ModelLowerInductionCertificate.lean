module
public import ModelBitsetExtensionalityCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def lowerInductionFormula (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 1 :=
 “n. (∃s, ∀k, !literalBitMembershipFormula k s ↔ !φ (k+n)) → ∃s, ∀k, !φ k ↔ !literalBitMembershipFormula k s”
lemma lowerInductionFormula_eval (φ : ArithmeticSemiformula Nat 1) (e : Nat → M) (n : M) :
 (lowerInductionFormula φ).Eval ![n] e ↔
 ((∃s,∀k,t120 s k ↔ φ.Eval ![k+n] e) → ∃s,∀k,φ.Eval ![k] e ↔ t120 s k) := by
 simp [lowerInductionFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,literalBitMembershipFormula_eval]
 simp

noncomputable def lowerInduction_certificate {e : Nat → M} {P : M → Prop}
 (p : FormulaCertificate e 1 (fun v => P (v 0))) :
 FormulaCertificate e 1 (fun v =>
 (∃s,∀k,t120 s k ↔ P (k+v 0)) → ∃s,∀k,P k ↔ t120 s k) where
 formula := lowerInductionFormula p.formula
 correct := by
   intro v
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
   rw [←hv,lowerInductionFormula_eval]
   simp only [←p.correct]
   rfl
end ZF209.MM0ModelReplay
