module
public import ModelLiteralBitMembershipCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalSetExtensional_iff (A B : M → Prop) : t17 A B ↔ ∀k, A k ↔ B k := by
 simp [t17,t8,t3,t2,t1,t0,t16,iff_def]
lemma literalSetInsertOr_iff (a b : Prop) : t4 a b ↔ a ∨ b := by
 simp [t4,t1,t0,or_iff_not_imp_left]
def literalInsertCodePredicate : ArithmeticSemiformula Nat 3 :=
 “s a b. ∀k, (!literalBitMembershipFormula k s ↔ (k=a ∨ !literalBitMembershipFormula k b))”
def literalInsertCode_certificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v=>t123 (v 0) (v 1)) := by
 let q : FormulaCertificate e 3 (fun v=>t17 (t120 (v 0)) (fun k=>t4 (t10 k (v 1)) (t120 (v 2) k))) := {
  formula := literalInsertCodePredicate
  correct := by
   intro v
   simp only [literalSetExtensional_iff,literalSetInsertOr_iff,t10]
   simp [literalInsertCodePredicate,Semiformula.eval_rew,Semiformula.eval_all,LogicalConnective.iff,Function.comp_def,Matrix.comp_vecCons']
   have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
    funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
   simp only [hv, ←iff_def]
   change (∀k, t120 (v 0) k ↔ (k=v 1 ∨ t120 (v 2) k)) ↔ (∀k, literalBitMembershipFormula.Eval ![k,v 0] e ↔ (k=v 1 ∨ literalBitMembershipFormula.Eval ![k,v 2] e))
   simp only [literalBitMembershipFormula_eval] }
 exact FunctionGraphCertificate.ofDescription q
end ZF207.MM0ModelReplay
