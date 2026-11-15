module
public import ExactContextWfModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelSourceContextWf_branch (n : M) :
 contextWfBranchGraph.val.Evalb ![modelSourceContextWfCode n,
 (sourceContextWfHistory (M := M)).result ![] n,n,modelListHead n,modelListTail n] := by
 have h := modelSourceContextWfCode_step n
 exact (graphValue_spec contextWfBranchGraph contextWfBranchGraph_total _ _).mpr h

lemma modelSourceContextWf_raw (n : M) : modelSourceContextWf n ↔
 n=0 ∨ (modelSourceWf (modelListHead n) ∧
 znth ((sourceContextWfHistory (M := M)).result ![] n) (modelListTail n)=1) := by
 have h := (contextWfBranchGraph_eval _ _ _ _ _).mp (modelSourceContextWf_branch n)
 by_cases hp : n=0 ∨ (modelSourceWf (modelListHead n) ∧
   znth ((sourceContextWfHistory (M := M)).result ![] n) (modelListTail n)=1)
 · have hz : modelSourceContextWfCode n=1 := by simpa [hp] using h
   simp [modelSourceContextWf,hz,hp]
 · have hz : modelSourceContextWfCode n=0 := by simpa [hp] using h
   simp [modelSourceContextWf,hz,hp]

lemma modelSourceContextWf_zero : modelSourceContextWf (0:M) :=
 (modelSourceContextWf_raw 0).mpr (Or.inl rfl)

lemma modelSourceContextWf_step (n : M) (hn : 0<n) :
 modelSourceContextWf n ↔ modelSourceWf (modelListHead n) ∧ modelSourceContextWf (modelListTail n) := by
 rw [modelSourceContextWf_raw,modelSourceContextWfCode_lookup _ _ (modelListTail_lt n hn)]
 simp only [ne_of_gt hn,false_or,modelSourceContextWf]

lemma modelSourceContextWf_cons (a b : M) :
 modelSourceContextWf (modelListCons a b) ↔ modelSourceWf a ∧ modelSourceContextWf b := by
 rw [modelSourceContextWf_step _ (by simp [modelListCons]),modelListHead_cons,modelListTail_cons]

end ZFR.ArithmeticRepresentation
