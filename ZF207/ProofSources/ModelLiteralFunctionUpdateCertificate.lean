module
public import ModelLiteralSetCodeCertificate
public import LiteralProjectionModelAlignment
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalFunctionUpdate_member (k s a b : M) :
 t136 (t120 s) a b k ↔
 ((t64 k=a ∧ t65 k=b) ∨ (t64 k≠a ∧ t120 s k)) := by
 have hp : t63 (t64 k) (t65 k)=k := by
  rw [literalPair_modelCantor,literalFst_modelUnpairLeft,literalSnd_modelUnpairRight]
  exact modelUnpair_reconstruct k
 simp [t136,t73,t15,t16,t25,t14,t8,t0,t10,t5,t4,t2,t1,hp,or_iff_not_imp_left]
def literalFunctionUpdatePredicate : ArithmeticSemiformula Nat 4 :=
 “k s a b. ∃x, ∃y, !unpairLeftGraph x k ∧ !unpairRightGraph y k ∧ ((x=a ∧ y=b) ∨ (x≠a ∧ !literalBitMembershipFormula k s))”
lemma literalFunctionUpdatePredicate_eval (e : Nat → M) (k s a b : M) :
 literalFunctionUpdatePredicate.Eval ![k,s,a,b] e ↔ t136 (t120 s) a b k := by
 have hl (x k:M) : unpairLeftGraph.val.Evalb ![x,k] ↔ x=t64 k := by
  rw [literalFst_modelUnpairLeft]; exact graphValue_spec unpairLeftGraph unpairLeftGraph_total x ![k]
 have hr (x k:M) : unpairRightGraph.val.Evalb ![x,k] ↔ x=t65 k := by
  rw [literalSnd_modelUnpairRight]; exact graphValue_spec unpairRightGraph unpairRightGraph_total x ![k]
 simp [literalFunctionUpdatePredicate,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp only [hl,hr,literalBitMembershipFormula_eval,exists_eq_left]
 exact (literalFunctionUpdate_member k s a b).symm

def literalFunctionUpdateCodePredicate : ArithmeticSemiformula Nat 4 :=
 “c s a b. ∀k, (!literalBitMembershipFormula k c ↔ !literalFunctionUpdatePredicate k s a b)”
lemma literalFunctionUpdateCodePredicate_eval (e : Nat → M) (c s a b : M) :
 literalFunctionUpdateCodePredicate.Eval ![c,s,a,b] e ↔ t17 (t120 c) (t136 (t120 s) a b) := by
 rw [literalSetExtensional_iff]
 simp [literalFunctionUpdateCodePredicate,Semiformula.eval_rew,LogicalConnective.iff,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv, ←iff_def]
 simp only [literalBitMembershipFormula_eval,literalFunctionUpdatePredicate_eval]

def literalFunctionUpdateCode_certificate (e : Nat → M) :
 FunctionGraphCertificate e 3 (fun v=>t121 (t136 (t120 (v 0)) (v 1) (v 2))) := by
 let q : FormulaCertificate e 4 (fun v=>t17 (t120 (v 0)) (t136 (t120 (v 1)) (v 2) (v 3))) := {
  formula := literalFunctionUpdateCodePredicate
  correct := by
   intro v
   have hv : ![v 0,v 1,v 2,v 3]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.cases rfl (fun m=>Fin.elim0 m) l) k) j) i
   rw [←hv]
   exact (literalFunctionUpdateCodePredicate_eval e (v 0) (v 1) (v 2) (v 3)).symm }
 exact FunctionGraphCertificate.ofDescription q
end ZF207.MM0ModelReplay
