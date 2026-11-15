module
public import ExactContextShiftModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelSourceContextShift_branch (n : M) :
 contextShiftBranchGraph.val.Evalb ![modelSourceContextShift n,
 (sourceContextShiftHistory (M := M)).result ![] n,n,modelListHead n,modelListTail n] := by
 have h := modelSourceContextShift_step n
 exact (graphValue_spec contextShiftBranchGraph contextShiftBranchGraph_total _ _).mpr h

lemma modelSourceContextShift_zero : modelSourceContextShift (0:M)=0 := by
 have h := (contextShiftBranchGraph_eval _ _ _ _ _).mp (modelSourceContextShift_branch (0:M))
 simpa using h

lemma modelSourceContextShift_cons_step (n : M) (hn : 0<n) :
 modelSourceContextShift n=modelListCons (modelSourceShift 0 (modelListHead n))
   (modelSourceContextShift (modelListTail n)) := by
 have h := (contextShiftBranchGraph_eval _ _ _ _ _).mp (modelSourceContextShift_branch n)
 have he : modelSourceContextShift n=modelListCons (modelSourceShift 0 (modelListHead n))
   (znth ((sourceContextShiftHistory (M := M)).result ![] n) (modelListTail n)) := by
   simpa [ne_of_gt hn] using h
 rw [modelSourceContextShift_lookup _ _ (modelListTail_lt n hn)] at he
 exact he

lemma modelSourceContextShift_cons (a b : M) :
 modelSourceContextShift (modelListCons a b)=modelListCons (modelSourceShift 0 a) (modelSourceContextShift b) := by
 rw [modelSourceContextShift_cons_step _ (by simp [modelListCons]),modelListHead_cons,modelListTail_cons]

end ZFR.ArithmeticRepresentation
