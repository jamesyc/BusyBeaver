module
public import ModelLiteralRecursionCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The initial value and index are bound arguments; function parameters retain their original assignment. -/
def literalRecHistoryBinaryFormula (app : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 3 :=
 “y n a. ∃s, !literalPsetApplicationGraph a 0 s ∧ !literalPsetApplicationGraph y n s ∧
 ∀k, k<n → ∃u, ∃v, !literalPsetApplicationGraph u k s ∧ !literalPsetApplicationGraph v (k+1) s ∧ !app v u”
lemma literalRecHistoryBinaryFormula_eval {e : Nat → M} {A : M → Prop}
 (g : FunctionGraphCertificate e 1 (fun v=>t84 A (v 0))) (y n a0 : M) :
 (literalRecHistoryBinaryFormula g.formula).Eval ![y,n,a0] e ↔
 ∃s,t84 (t109 s) 0=a0 ∧ t84 (t109 s) n=y ∧
 ∀k,k<n → t84 (t109 s) (k+1)=t84 A (t84 (t109 s) k) := by
 have hg (z x : M) : g.formula.Eval ![z,x] e ↔ z=t84 A x := g.correct ![x] z
 simp [literalRecHistoryBinaryFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp [literalPsetApplicationGraph_eval,hg,eq_comm]

/-- No recursion theorem is assumed: this is the literal unique-or-zero description graph. -/
def literalRecursionBinary_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 2 (fun v=>t110 (v 1) A (v 0)) := by
 let g := literalApply_certificate a
 let p : FormulaCertificate e 3 (fun v=>
  ∃s,t84 (t109 s) 0=v 2 ∧ t84 (t109 s) (v 1)=v 0 ∧
  ∀k,k<v 1 → t84 (t109 s) (k+1)=t84 A (t84 (t109 s) k)) := {
  formula := literalRecHistoryBinaryFormula g.formula
  correct := by
   intro v
   have hv : ![v 0,v 1,v 2]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.elim0 l) k) j) i
   rw [←hv]
   exact (literalRecHistoryBinaryFormula_eval g (v 0) (v 1) (v 2)).symm }
 let out := FunctionGraphCertificate.ofDescription p
 refine ⟨out.formula,?_⟩
 intro v y
 rw [out.correct]
 unfold t110 t40 t15
 classical
 simp [t9,t1,t8,t2,t0,t10,t28,t29,literalLt_order,and_assoc]
end ZF209.MM0ModelReplay
