module
public import ModelLiteralPsetMembershipCertificate
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Both the member and set code are bound arithmetic arguments. -/
def literalPsetBinaryFormula : ArithmeticSemiformula Nat 2 :=
 “k s. ∃b, ∃c, !unpairLeftGraph b s ∧ !unpairRightGraph c s ∧ !mm0BetaMembershipFormula k b c”
lemma literalPsetBinaryFormula_eval (e : Nat → M) (k s : M) :
 literalPsetBinaryFormula.Eval ![k,s] e ↔ t109 s k := by
 have hl (b s : M) : unpairLeftGraph.val.Evalb ![b,s] ↔ b=modelUnpairLeft s :=
  graphValue_spec unpairLeftGraph unpairLeftGraph_total b ![s]
 have hr (c s : M) : unpairRightGraph.val.Evalb ![c,s] ↔ c=modelUnpairRight s :=
  graphValue_spec unpairRightGraph unpairRightGraph_total c ![s]
 simp [literalPsetBinaryFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
 Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change (∃b,unpairLeftGraph.val.Evalb ![b,s] ∧ ∃c,unpairRightGraph.val.Evalb ![c,s] ∧ mm0BetaMembershipFormula.Eval ![k,b,c] e) ↔ _
 simp only [hl,hr,exists_eq_left,mm0BetaMembership_eval]
 exact (literalPset_unpair s k).symm

def literalPsetApplicationPredicate : ArithmeticSemiformula Nat 3 :=
 “y x s. ∃p, !literalPairGraph p x y ∧ !literalPsetBinaryFormula p s”
lemma literalPsetApplicationPredicate_eval (e : Nat → M) (y x s : M) :
 literalPsetApplicationPredicate.Eval ![y,x,s] e ↔ t109 s (t63 x y) := by
 simp [literalPsetApplicationPredicate,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change (∃p,literalPairGraph.Eval ![p,x,y] e ∧ literalPsetBinaryFormula.Eval ![p,s] e) ↔ _
 simp only [literalPairGraph_eval,literalPsetBinaryFormula_eval,exists_eq_left]

def literalPsetApplication_certificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v=>t84 (t109 (v 1)) (v 0)) := by
 let p : FormulaCertificate e 3 (fun v=>t109 (v 2) (t63 (v 1) (v 0))) := {
  formula := literalPsetApplicationPredicate
  correct := by
   intro v
   have hv : ![v 0,v 1,v 2]=v := by
    funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.elim0 l) k) j) i
   rw [←hv]
   exact (literalPsetApplicationPredicate_eval e (v 0) (v 1) (v 2)).symm }
 exact FunctionGraphCertificate.ofDescription p
end ZF209.MM0ModelReplay
