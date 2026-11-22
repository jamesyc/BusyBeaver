module
public import ZF192Support.Coding.Lists.MemberStepGraph
@[expose] public section
namespace ZFR.ArithmeticRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
/-- Course-of-values append on internal Cantor-list codes, not host lists. -/
def appendStepGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z h n b. (n=0 ∧ z=b) ∨ (n≠0 ∧ ∃ a, ∃ t, ∃ u,
 !listHeadGraph a n ∧ !listTailGraph t n ∧ !znthDef u h t ∧ !listConsGraph z a u)”
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma appendStepGraph_eval (z h n b : M) : appendStepGraph.val.Evalb ![z,h,n,b] ↔
 (n=0 ∧ z=b) ∨ (n≠0 ∧ z=modelListCons (modelListHead n) (znth h (modelListTail n))) := by
 simp [appendStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
  Matrix.comp_vecCons',Matrix.empty_eq,znth_defined.iff,listConsGraph_eval]
 simp only [Matrix.constant_eq_singleton]
 simp [listHeadGraph_eval,listTailGraph_eval,listConsGraph_eval]
lemma appendStepGraph_total : GraphTotalIn (M := M) appendStepGraph := by
 intro v
 rw [Matrix.fun_eq_vec_three v]
 simp only [appendStepGraph_eval]
 by_cases hn : v 1=0 <;> simp [hn]
noncomputable def appendHistory : PR.Construction M (historyBlueprint appendStepGraph) :=
 historyConstruction appendStepGraph appendStepGraph_total
noncomputable def modelListAppend (n b : M) : M := znth (appendHistory.result ![b] (n+1)) n
lemma modelListAppend_step (n b : M) : appendStepGraph.val.Evalb
 ![modelListAppend n b,appendHistory.result ![b] n,n,b] := by
 unfold modelListAppend appendHistory
 rw [history_last]
 exact (graphValue_spec appendStepGraph appendStepGraph_total _ _).mpr rfl
lemma modelListAppend_lookup (b n w : M) (hn : n<w) :
 znth (appendHistory.result ![b] w) n=modelListAppend n b :=
 history_stable appendStepGraph appendStepGraph_total ![b] n (n+1) w
   (lt_add_one _) (succ_le_iff_lt.mpr hn)
@[simp] theorem modelListAppend_zero (b : M) : modelListAppend 0 b=b := by
 have h := (appendStepGraph_eval _ _ _ _).mp (modelListAppend_step 0 b)
 simpa using h
@[simp] theorem modelListAppend_cons (a t b : M) :
 modelListAppend (modelListCons a t) b=modelListCons a (modelListAppend t b) := by
 have h := (appendStepGraph_eval _ _ _ _).mp (modelListAppend_step (modelListCons a t) b)
 have hn : 0<modelListCons a t := by simp [modelListCons]
 have ht : t<modelListCons a t := by simpa only [modelListTail_cons] using modelListTail_lt _ hn
 rw [modelListHead_cons,modelListTail_cons,modelListAppend_lookup b t _ ht] at h
 simpa [ne_of_gt hn] using h
def appendGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n b. ∃ h, !(historyBlueprint appendStepGraph).resultDef h (n+1) b ∧ !znthDef z h n”
lemma appendGraph_eval (z n b : M) : appendGraph.val.Evalb ![z,n,b] ↔ z=modelListAppend n b := by
 let c := appendHistory (M := M)
 simp [appendGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
  Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 simp only [Matrix.constant_eq_singleton]
 simp [modelListAppend]
 rfl
lemma appendGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelListAppend (M := M)) appendGraph := by
 refine .mk ?_
 intro v
 rw [Matrix.fun_eq_vec_three v]
 exact appendGraph_eval _ _ _
end ZFR.ArithmeticRepresentation
