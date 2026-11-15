module
public import LiteralPsetModelAlignment
public import LiteralProjectionModelAlignment
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalPair_projections (s : M) : t63 (t64 s) (t65 s)=s := by
 rw [literalPair_modelCantor,literalFst_modelUnpairLeft,literalSnd_modelUnpairRight,modelUnpair_reconstruct]
lemma literalPset_unpair (s k : M) : t109 s k ↔ mm0BetaMembership (modelUnpairLeft s) (modelUnpairRight s) k := by
 have h := literalPset_beta (t64 s) (t65 s) k
 rw [literalPair_projections,literalFst_modelUnpairLeft,literalSnd_modelUnpairRight] at h
 exact h
/-- Free parameter zero is the actual set code, not a standard numeral. -/
def literalPsetMembershipFormula : ArithmeticSemiformula Nat 1 :=
 “k. ∃b, ∃c, !unpairLeftGraph b &0 ∧ !unpairRightGraph c &0 ∧ !mm0BetaMembershipFormula k b c”
lemma literalPsetMembershipFormula_eval (e : Nat → M) (k : M) :
 literalPsetMembershipFormula.Eval ![k] e ↔ t109 (e 0) k := by
 have hl (b s : M) : unpairLeftGraph.val.Evalb ![b,s] ↔ b=modelUnpairLeft s :=
  graphValue_spec unpairLeftGraph unpairLeftGraph_total b ![s]
 have hr (c s : M) : unpairRightGraph.val.Evalb ![c,s] ↔ c=modelUnpairRight s :=
  graphValue_spec unpairRightGraph unpairRightGraph_total c ![s]
 simp [literalPsetMembershipFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
 Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change (∃b,unpairLeftGraph.val.Evalb ![b,e 0] ∧ ∃c,unpairRightGraph.val.Evalb ![c,e 0] ∧ mm0BetaMembershipFormula.Eval ![k,b,c] e) ↔ _
 simp only [hl,hr,exists_eq_left,mm0BetaMembership_eval]
 exact (literalPset_unpair (e 0) k).symm

def literalPsetMembership_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t109 (e 0) (v 0)) where
 formula := literalPsetMembershipFormula
 correct := by
  intro v
  have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
  rw [←hv]
  exact (literalPsetMembershipFormula_eval e (v 0)).symm
end ZF209.MM0ModelReplay
