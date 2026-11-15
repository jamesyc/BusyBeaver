module
public import ExactRowCodingGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma branchesGraph_defined : 𝚺ᴬ₁.Defined (fun v : Fin 5 → M => v 0=modelBranches (v 1) (v 2) (v 3) (v 4)) branchesGraph := .mk (by
 intro v
 simp [branchesGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,rowCantor_defined.iff,modelBranches])

def rowWfFormula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “r. (∃ g, ∃ a, !sequentGraph r g a ∧ !sourceContextWfFormula g ∧ !sourceWfFormula a) ∨
 (∃ g, ∃ a, ∃ b, ∃ c, !branchesGraph r g a b c ∧ !sourceContextWfFormula g ∧ !sourceWfFormula a ∧ !sourceWfFormula b ∧ !sourceWfFormula c)”
def modelRowWf (r : M) : Prop :=
 (∃ g a, r=modelSequent g a ∧ modelSourceContextWf g ∧ modelSourceWf a) ∨
 (∃ g a b c, r=modelBranches g a b c ∧ modelSourceContextWf g ∧ modelSourceWf a ∧ modelSourceWf b ∧ modelSourceWf c)
lemma rowWfFormula_defined : 𝚺ᴬ₁.DefinedPred (modelRowWf (M:=M)) rowWfFormula := .mk (by
 intro v
 simp [rowWfFormula,modelRowWf,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 sequentGraph_defined.iff,branchesGraph_defined.iff,sourceContextWfFormula_defined.iff,sourceWfFormula_defined.iff])
lemma modelRowWf_nat (r : Nat) : modelRowWf r ↔ sourceRowWf r := by
 simp only [modelRowWf,modelSequent_nat,modelBranches_nat,modelSourceContextWf_nat,modelSourceWf_nat]
 constructor
 · rintro (⟨g,a,rfl,hg,ha⟩|⟨g,a,b,c,rfl,hg,ha,hb,hc⟩)
   · simpa [sourceRowWf,sourceSequent,sourceUnpair_pair] using And.intro hg ha
   · simpa [sourceRowWf,sourceBranches,sourceUnpair_pair] using And.intro hg (And.intro ha (And.intro hb hc))
 · intro h
   unfold sourceRowWf at h
   dsimp only at h
   split at h
   · rename_i hz
     left
     refine ⟨_,_,?_,h⟩
     unfold sourceSequent
     rw [C209Soundness.unpair_spec,←hz,C209Soundness.unpair_spec]
   · rename_i hn
     right
     obtain ⟨h1,hg,ha,hb,hc⟩ := h
     refine ⟨_,_,_,_,?_,hg,ha,hb,hc⟩
     unfold sourceBranches
     rw [C209Soundness.unpair_spec,C209Soundness.unpair_spec,C209Soundness.unpair_spec,←h1,C209Soundness.unpair_spec]
end ZFR.ArithmeticRepresentation
