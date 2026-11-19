module
public import ExactMemberDefinability
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def contextSubStepGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z s g h. (g=0 ∧ z=1) ∨ (g≠0 ∧ ∃ a, ∃ b, ∃ u, ∃ v,
 !listHeadGraph a g ∧ !listTailGraph b g ∧ !memberCodeGraph u a h ∧ !znthDef v s b ∧
 ((u=1 ∧ v=1 ∧ z=1) ∨ (¬(u=1 ∧ v=1) ∧ z=0)))”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma contextSubStepGraph_eval (z s g h : M) : contextSubStepGraph.val.Evalb ![z,s,g,h] ↔
 (g=0 ∧ z=1) ∨ (g≠0 ∧
 ((modelMember (modelListHead g) h ∧ znth s (modelListTail g)=1 ∧ z=1) ∨
 (¬(modelMember (modelListHead g) h ∧ znth s (modelListTail g)=1) ∧ z=0))) := by
 simp [contextSubStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,memberCodeGraph_defined.iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
  funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp [listHeadGraph_eval,listTailGraph_eval,modelMember,eq_comm]
 <;> tauto

lemma contextSubStepGraph_total : GraphTotalIn (M := M) contextSubStepGraph := by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 simp only [contextSubStepGraph_eval]
 by_cases hg : v 1=0
 · simp [hg]
 · by_cases hm : modelMember (modelListHead (v 1)) (v 2) <;>
   by_cases ht : znth (v 0) (modelListTail (v 1))=1 <;> simp [hg,hm,ht]

noncomputable def contextSubHistory : PR.Construction M (historyBlueprint contextSubStepGraph) :=
 historyConstruction contextSubStepGraph contextSubStepGraph_total
noncomputable def modelContextSubCode (g h : M) : M := znth (contextSubHistory.result ![h] (g+1)) g
def modelContextSub (g h : M) : Prop := modelContextSubCode g h=1

lemma modelContextSub_step (g h : M) : contextSubStepGraph.val.Evalb
 ![modelContextSubCode g h, contextSubHistory.result ![h] g,g,h] := by
 unfold modelContextSubCode contextSubHistory
 rw [history_last]
 exact (graphValue_spec contextSubStepGraph contextSubStepGraph_total _ _).mpr rfl

lemma modelContextSub_lookup (g h w : M) (hg : g<w) :
 znth (contextSubHistory.result ![h] w) g=modelContextSubCode g h :=
 history_stable contextSubStepGraph contextSubStepGraph_total ![h] g (g+1) w
   (lt_add_one _) (succ_le_iff_lt.mpr hg)

lemma modelContextSubCode_zero (h : M) : modelContextSubCode 0 h=1 := by
 have hx := (contextSubStepGraph_eval _ _ _ _).mp (modelContextSub_step 0 h)
 simpa using hx

lemma modelContextSub_cons (a b h : M) : modelContextSub (modelListCons a b) h ↔
 modelMember a h ∧ modelContextSub b h := by
 have hx := (contextSubStepGraph_eval _ _ _ _).mp (modelContextSub_step (modelListCons a b) h)
 have hn : 0<modelListCons a b := by simp [modelListCons]
 have hb : b<modelListCons a b := by
  have hh := modelListTail_lt (modelListCons a b) hn
  simpa only [modelListTail_cons] using hh
 rw [modelListHead_cons,modelListTail_cons,modelContextSub_lookup b h _ hb] at hx
 have hx' := hx.resolve_left (by rintro ⟨hz,_⟩; exact (ne_of_gt hn) hz)
 unfold modelContextSub
 rcases hx'.2 with ⟨hm,ht,hz⟩|⟨hm,hz⟩
 · simp [hz,hm,ht]
 · simp [hz,hm]

end ZFR.ArithmeticRepresentation
