module
public import ModelLiteralRecursionBinaryCertificate
public import ModelReplay1905
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalExponentHistoryFormula : ArithmeticSemiformula Nat 3 :=
 “y n b. ∃s, !literalPsetApplicationGraph 1 0 s ∧ !literalPsetApplicationGraph y n s ∧
 ∀k, k<n → ∃u, ∃v, !literalPsetApplicationGraph u k s ∧ !literalPsetApplicationGraph v (k+1) s ∧ v=b*u”
lemma literalExponentHistoryFormula_eval (e : Nat → M) (y n b : M) :
 literalExponentHistoryFormula.Eval ![y,n,b] e ↔
 ∃s,t84 (t109 s) 0=1 ∧ t84 (t109 s) n=y ∧
 ∀k,k<n → t84 (t109 s) (k+1)=b*t84 (t109 s) k := by
 simp [literalExponentHistoryFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp [literalPsetApplicationGraph_eval,eq_comm]

def literalExponent_certificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v=>t117 (v 1) (v 0)) := by
 let p : FormulaCertificate e 3 (fun v=>
  ∃s,t84 (t109 s) 0=1 ∧ t84 (t109 s) (v 1)=v 0 ∧
  ∀k,k<v 1 → t84 (t109 s) (k+1)=v 2*t84 (t109 s) k) := {
  formula := literalExponentHistoryFormula
  correct := by
   intro v
   have hv : ![v 0,v 1,v 2]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.elim0 l) k) j) i
   rw [←hv]
   exact (literalExponentHistoryFormula_eval e (v 0) (v 1) (v 2)).symm }
 let out := FunctionGraphCertificate.ofDescription p
 refine ⟨out.formula,?_⟩
 intro v y
 rw [out.correct]
 unfold t117 t110 t40 t15
 classical
 have happ (F : M → M) (x : M) : t84 (t82 F) x=F x := p1493 F x
 simp [t9,t1,t8,t2,t0,t10,t28,t29,t30,t45,literalLt_order,happ]
end ZF209.MM0ModelReplay
