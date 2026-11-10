import PA215.Source.CachedV2.OriginalCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PA215.Source.CachedV2
open PA215.Runtime PA215.Census
attribute [local irreducible] exactSites PA215.Census.all

def zeroChoice : Op → List Nat → Bool
  | .dec r,vs => decide (readFile vs r = 0)
  | _,_ => true

theorem chosen_branch_valid (op : Op) (vs : List Nat) (hv : 10 ≤ vs.length) :
    Valid (ObligationKeys.expectedBranch op (zeroChoice op vs)) vs := by
  cases op with
  | dec r =>
    rw [ObligationKeys.expectedBranch,valid_branch_iff]
    simp only [zeroChoice]
    by_cases hz : readFile vs r = 0 <;> simp [hz,hv]
  | inc r => exact ⟨hv,True.intro⟩
  | breakTo n => exact ⟨hv,True.intro⟩
  | continueTo n => exact ⟨hv,True.intro⟩
  | halt => exact ⟨hv,True.intro⟩

theorem originalAt_mem (j : Fin 5134) : originalAt j ∈ PA215.Census.all.toList :=
  Array.getElem_mem_toList (by simpa only [PA215.Census.all_size] using j.isLt)

theorem originalAt_agrees (j : Fin 5134) : recordAgrees (originalAt j) = true :=
  (List.all_eq_true.mp original_all_frames_agree) _ (originalAt_mem j)

/-- Select a real census index satisfying the actual physical-file branch,
while recovering the whole original/source frame agreement. -/
theorem selected_original (i : Nat) (s : Site) (vs : List Nat)
    (hs : exactSites[i]? = some s) (hv : 10 ≤ vs.length) :
    ∃ j : Fin 5134, (originalAt j).siteIndex = i ∧
      Valid (originalAt j).branch vs ∧ agreesWith s (originalAt j) = true := by
  obtain ⟨j,hi,hb⟩ := source_original_indexed i s (zeroChoice s.op vs) hs
  refine ⟨j,hi,?_,?_⟩
  · rw [hb]
    exact chosen_branch_valid s.op vs hv
  · have ha := originalAt_agrees j
    unfold recordAgrees at ha
    rw [hi,hs] at ha
    exact ha
#print axioms selected_original
end PA215.Source.CachedV2
