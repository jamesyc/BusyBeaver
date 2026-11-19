module
public import ModelLiteralFamilySizeCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalBitDomainFormula : ArithmeticSemiformula Nat 2 :=
 “k s. ∃y, ∃p, !literalPairGraph p k y ∧ !literalBitMembershipFormula p s”
lemma literalBitDomainFormula_eval (e : Nat → M) (k s : M) :
 literalBitDomainFormula.Eval ![k,s] e ↔ t76 (t120 s) k := by
 simp [literalBitDomainFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,literalPairGraph_eval,literalBitMembershipFormula_eval,exists_eq_left]
 simp [t76,t15,t9,t1,t8,t16]
def literalBitDomain_certificate (e : Nat → M) :
 FormulaCertificate e 2 (fun v=>t76 (t120 (v 1)) (v 0)) where
 formula := literalBitDomainFormula
 correct := by
  intro v
  have hv : ![v 0,v 1]=v := by
   funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
  rw [←hv]
  exact (literalBitDomainFormula_eval e (v 0) (v 1)).symm
def literalBitDomainSize_certificate (e : Nat → M) :
 FunctionGraphCertificate e 1 (fun v=>t125 (t76 (t120 (v 0)))) :=
 literalFamilySize_certificate (P:=fun k s=>t76 (t120 s) k) (literalBitDomain_certificate e)
end ZF207.MM0ModelReplay
