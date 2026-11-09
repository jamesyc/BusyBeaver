module

public import User211PAModelPrimitive
public import User211SourceEquivalence

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA211.UserCandidate.PA.ModelCoverageAssembler
open PA215.Source PA211.UserCandidate.PA.ModelPrimitive
/-- Generic assembly prevents reducing thousands of stored proof terms. -/
theorem coverage_of_entries
    (entries : Array (Entry PA211.UserCandidate.Source.path 3947))
    (sites_eq : entries.map (·.site)=PA211.UserCandidate.Source.sites)
    (codes_eq : entries.map (·.code)=PA213.SourceProgram.codes) :
    ∀ i, i<3947 → ∃ code, resolveAt exactSites i=some code ∧
      Implements PA211.UserCandidate.Source.path 3947 (PA211.UserCandidate.Source.path i) code := by
  have count_eq : entries.size=3947 := by
    have h := congrArg Array.size sites_eq
    simpa only [Array.size_map,PA211.UserCandidate.Source.sites_count] using h
  intro i hi
  have he : i < entries.size := by rw [count_eq]; exact hi
  let e := entries[i]
  have hs : some e.site = PA211.UserCandidate.Source.sites[i]? := by
    have h := congrArg (fun a => a[i]?) sites_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  have hc : some e.code = PA213.SourceProgram.codes[i]? := by
    have h := congrArg (fun a => a[i]?) codes_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  refine ⟨e.code,?_,?_⟩
  · rw [PA213.SourceEquivalence.baseline_resolve, ← hc]
  · have hp : PA211.UserCandidate.Source.path i = e.site.path := by
      rw [PA211.UserCandidate.Source.path_eq, ← hs]; rfl
    rw [hp]
    exact @Entry.proof _ _ e
#print axioms coverage_of_entries
end PA211.UserCandidate.PA.ModelCoverageAssembler
