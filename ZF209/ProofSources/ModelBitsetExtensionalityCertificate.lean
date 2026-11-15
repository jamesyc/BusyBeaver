module
public import ModelLiteralBitMembershipCertificate
public import ModelReplay2037
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def bitsetExtensionalityFormula : ArithmeticSemiformula Nat 1 :=
 “n. (∀k, k<n → (!literalBitMembershipFormula k &0 → !literalBitMembershipFormula k &1)) →
 ∃p, ∃u, ∃v, !literalExponentGraph p n 2 ∧ !literalRemainderGraph u &0 p ∧ !literalRemainderGraph v &1 p ∧ u≤v”
lemma bitsetExtensionalityFormula_eval (e : Nat → M) (n : M) :
 bitsetExtensionalityFormula.Eval ![n] e ↔
 ((∀k,k<n → t120 (e 0) k → t120 (e 1) k) →
 t57 (e 0) (t117 2 n) ≤ t57 (e 1) (t117 2 n)) := by
 simp [bitsetExtensionalityFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp only [literalBitMembershipFormula_eval,literalExponentGraph_eval,literalRemainderGraph_eval,exists_eq_left]
 simp

noncomputable def bitsetExtensionality_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v =>
 (∀k,k<v 0 → t120 (e 0) k → t120 (e 1) k) →
 t57 (e 0) (t117 2 (v 0)) ≤ t57 (e 1) (t117 2 (v 0))) where
 formula := bitsetExtensionalityFormula
 correct := by
   intro v
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
   rw [←hv]
   exact (bitsetExtensionalityFormula_eval e (v 0)).symm
end ZF209.MM0ModelReplay
