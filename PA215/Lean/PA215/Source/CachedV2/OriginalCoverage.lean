import PA215.Source.OriginalObligationKeys
import PA215.Source.CensusCompatibility
import PA215.Source.CachedV2.AllContractFrames
namespace PA215.Source.CachedV2
attribute [local irreducible] exactSites PA215.Census.all

/-- The input census covers every exact source site and every admissible
branch. This is the direction not supplied by checking each original record. -/
theorem source_original_exists (i : Nat) (s : Site) (z : Bool)
    (hs : exactSites[i]? = some s) :
    ∃ r ∈ PA215.Census.all.toList, r.siteIndex = i ∧
      r.branch = ObligationKeys.expectedBranch s.op z := by
  apply ObligationKeys.coverage exactSites.toList PA215.Census.all.toList
  · exact ObligationKeys.original_keys.trans ObligationKeys.exact_required.symm
  · intro r hr
    exact ObligationKeys.record_compatible ((List.all_eq_true.mp original_all_frames_agree) r hr)
  · simpa only [Array.getElem?_toList] using hs

/-- Concrete original index for each source branch, ready for the independently
indexed runtime registry; no bare numeric-ID trust or assumed surjectivity. -/
theorem source_original_indexed (i : Nat) (s : Site) (z : Bool)
    (hs : exactSites[i]? = some s) :
    ∃ j : Fin 5134, (PA215.Census.originalAt j).siteIndex = i ∧
      (PA215.Census.originalAt j).branch = ObligationKeys.expectedBranch s.op z := by
  obtain ⟨r,hr,hi,hb⟩ := source_original_exists i s z hs
  have hm := Array.mem_toList_iff.mp hr
  obtain ⟨k,hk,he⟩ := Array.mem_iff_getElem.mp hm
  let j : Fin 5134 := ⟨k,by simpa only [PA215.Census.all_size] using hk⟩
  have hj : PA215.Census.originalAt j = r := he
  exact ⟨j,by simpa only [hj] using hi,by simpa only [hj] using hb⟩

#print axioms source_original_exists
#print axioms source_original_indexed
end PA215.Source.CachedV2
