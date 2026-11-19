module
public import ModelLiteralPsetBinaryCertificate
public import ModelLiteralApplicationCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalPsetApplicationGraph : ArithmeticSemiformula Nat 3 :=
 descriptionGraph literalPsetApplicationPredicate
lemma literalPsetApplicationGraph_eval (e : Nat → M) (y x s : M) :
 literalPsetApplicationGraph.Eval ![y,x,s] e ↔ y=t84 (t109 s) x :=
 (literalPsetApplication_certificate e).correct ![x,s] y
/-- Free parameter zero is the initial value. The function graph retains its original free assignment. -/
def literalRecHistoryFormula (app : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “y n. ∃s, !literalPsetApplicationGraph &0 0 s ∧ !literalPsetApplicationGraph y n s ∧
 ∀k, k<n → ∃u, ∃v, !literalPsetApplicationGraph u k s ∧ !literalPsetApplicationGraph v (k+1) s ∧ !app v u”
lemma literalRecHistoryFormula_eval {e : Nat → M} {A : M → Prop}
 (g : FunctionGraphCertificate e 1 (fun v=>t84 A (v 0))) (y n : M) :
 (literalRecHistoryFormula g.formula).Eval ![y,n] e ↔
 ∃s,t84 (t109 s) 0=e 0 ∧ t84 (t109 s) n=y ∧
 ∀k,k<n → t84 (t109 s) (k+1)=t84 A (t84 (t109 s) k) := by
 have hg (z x : M) : g.formula.Eval ![z,x] e ↔ z=t84 A x := g.correct ![x] z
 simp [literalRecHistoryFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp [literalPsetApplicationGraph_eval,hg,eq_comm]

/-- No recursion theorem is assumed: this is the literal unique-or-zero description graph. -/
def literalRecursion_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t110 (e 0) A (v 0)) := by
 let g := literalApply_certificate a
 let p : FormulaCertificate e 2 (fun v=>
  ∃s,t84 (t109 s) 0=e 0 ∧ t84 (t109 s) (v 1)=v 0 ∧
  ∀k,k<v 1 → t84 (t109 s) (k+1)=t84 A (t84 (t109 s) k)) := {
  formula := literalRecHistoryFormula g.formula
  correct := by
   intro v
   have hv : ![v 0,v 1]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
   rw [←hv]
   exact (literalRecHistoryFormula_eval g (v 0) (v 1)).symm }
 let out := FunctionGraphCertificate.ofDescription p
 refine ⟨out.formula,?_⟩
 intro v y
 rw [out.correct]
 unfold t110 t40 t15
 classical
 simp [t9,t1,t8,t2,t0,t10,t28,t29,literalLt_order,and_assoc]
end ZF207.MM0ModelReplay
