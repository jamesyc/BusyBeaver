module
public import ZF192Support.Coding.Lists.DecoderGraphs
public import ZF192Support.Coding.Arithmetic.CourseOfValuesSentences
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def memberStepGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z h n x. (n=0 ∧ z=0) ∨ (n≠0 ∧ ∃ a, ∃ b, ∃ u,
 !listHeadGraph a n ∧ !listTailGraph b n ∧ !znthDef u h b ∧
 (((a=x ∨ u=1) ∧ z=1) ∨ ((a≠x ∧ u≠1) ∧ z=0)))”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma memberStepGraph_eval (z h n x : M) : memberStepGraph.val.Evalb ![z,h,n,x] ↔
 (n=0 ∧ z=0) ∨ (n≠0 ∧
 (((modelListHead n=x ∨ znth h (modelListTail n)=1) ∧ z=1) ∨
 ((modelListHead n≠x ∧ znth h (modelListTail n)≠1) ∧ z=0))) := by
 simp [memberStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,znth_defined.iff]
 simp only [Matrix.constant_eq_singleton]
 simp [listHeadGraph_eval,listTailGraph_eval]

lemma memberStepGraph_total : GraphTotalIn (M := M) memberStepGraph := by
 classical
 intro v
 rw [Matrix.fun_eq_vec_three v]
 simp only [memberStepGraph_eval]
 by_cases hn : v 1=0
 · simp [hn]
 · by_cases ha : modelListHead (v 1)=v 2 <;>
   by_cases hb : znth (v 0) (modelListTail (v 1))=1 <;> simp [hn,ha,hb]

noncomputable def memberHistory : PR.Construction M (historyBlueprint memberStepGraph) :=
 historyConstruction memberStepGraph memberStepGraph_total
noncomputable def modelMemberCode (x n : M) : M := znth (memberHistory.result ![x] (n+1)) n
def modelMember (x n : M) : Prop := modelMemberCode x n=1

lemma modelMember_step (x n : M) : memberStepGraph.val.Evalb
 ![modelMemberCode x n, memberHistory.result ![x] n,n,x] := by
 unfold modelMemberCode memberHistory
 rw [history_last]
 exact (graphValue_spec memberStepGraph memberStepGraph_total _ _).mpr rfl

lemma modelMember_lookup (x n w : M) (hn : n<w) :
 znth (memberHistory.result ![x] w) n=modelMemberCode x n :=
 history_stable memberStepGraph memberStepGraph_total ![x] n (n+1) w
   (lt_add_one _) (succ_le_iff_lt.mpr hn)

lemma modelMemberCode_zero (x : M) : modelMemberCode x 0=0 := by
 have h := (memberStepGraph_eval _ _ _ _).mp (modelMember_step x 0)
 simpa using h

lemma modelMember_cons (x a b : M) : modelMember x (modelListCons a b) ↔ a=x ∨ modelMember x b := by
 have h := (memberStepGraph_eval _ _ _ _).mp (modelMember_step x (modelListCons a b))
 have hn : 0<modelListCons a b := by simp [modelListCons]
 have hb : b<modelListCons a b := by
   have hh := modelListTail_lt (modelListCons a b) hn
   simpa only [modelListTail_cons] using hh
 rw [modelListHead_cons,modelListTail_cons,modelMember_lookup x b _ hb] at h
 have h' := h.resolve_left (by rintro ⟨hz,_⟩; exact (ne_of_gt hn) hz)
 unfold modelMember
 rcases h'.2 with ⟨hp,hz⟩|⟨hp,hz⟩
 · simp [hz,hp]
 · simp [hz,hp.1,hp.2]

end ZFR.ArithmeticRepresentation
