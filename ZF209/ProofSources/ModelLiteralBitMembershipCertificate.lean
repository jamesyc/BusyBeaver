module
public import ModelLiteralExponentCertificate
public import ModelLiteralRemainderCertificate
public import LiteralSourcePredicateDefinitions
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalExponentGraph : ArithmeticSemiformula Nat 3 := descriptionGraph literalExponentHistoryFormula
lemma literalExponentGraph_eval (e : Nat → M) (y n b : M) :
 literalExponentGraph.Eval ![y,n,b] e ↔ y=t117 b n := (literalExponent_certificate e).correct ![n,b] y
lemma literalDivisionGraph_eval (e : Nat → M) (q a b : M) :
 (descriptionGraph literalDivisionPredicate).Eval ![q,a,b] e ↔ q=t56 a b :=
 (literalDivisionCertificate e).correct ![a,b] q
/-- Both bit index and original binary-set code are bound arithmetic arguments. -/
def literalBitMembershipFormula : ArithmeticSemiformula Nat 2 :=
 “k s. ∃p, ∃q, !literalExponentGraph p k 2 ∧ !(descriptionGraph literalDivisionPredicate) q s p ∧ !literalRemainderGraph 1 q 2”
lemma literalBitMembershipFormula_eval (e : Nat → M) (k s : M) :
 literalBitMembershipFormula.Eval ![k,s] e ↔ t120 s k := by
 simp [literalBitMembershipFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp only [literalExponentGraph_eval,literalDivisionGraph_eval,literalRemainderGraph_eval,exists_eq_left]
 simp [t120,t15,t62,t119,t31,t30,t29,t28,t10,eq_comm,one_add_one_eq_two]

def literalBitApplicationPredicate : ArithmeticSemiformula Nat 3 :=
 “y x s. ∃p, !literalPairGraph p x y ∧ !literalBitMembershipFormula p s”
lemma literalBitApplicationPredicate_eval (e : Nat → M) (y x s : M) :
 literalBitApplicationPredicate.Eval ![y,x,s] e ↔ t120 s (t63 x y) := by
 simp [literalBitApplicationPredicate,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change (∃p,literalPairGraph.Eval ![p,x,y] e ∧ literalBitMembershipFormula.Eval ![p,s] e) ↔ _
 simp only [literalPairGraph_eval,literalBitMembershipFormula_eval,exists_eq_left]
def literalBitApplication_certificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v=>t84 (t120 (v 1)) (v 0)) := by
 let p : FormulaCertificate e 3 (fun v=>t120 (v 2) (t63 (v 1) (v 0))) := {
  formula := literalBitApplicationPredicate
  correct := by
   intro v
   have hv : ![v 0,v 1,v 2]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.elim0 l) k) j) i
   rw [←hv]
   exact (literalBitApplicationPredicate_eval e (v 0) (v 1) (v 2)).symm }
 exact FunctionGraphCertificate.ofDescription p
end ZF209.MM0ModelReplay
