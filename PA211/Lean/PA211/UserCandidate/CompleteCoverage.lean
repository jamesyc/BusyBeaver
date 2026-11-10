import PA211.UserCandidate.RuntimeCoverage
import User211SourceEquivalence
import PA211.UserCandidate.CompilerCorrectness
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA211.UserCandidate.CompleteCoverage
open PA215.Source PA211.UserCandidate.Source PA211.UserCandidate.PrimitiveSimulation PA211.UserCandidate.RuntimeCoverage

theorem coverage : PA211.UserCandidate.CompilerCorrectness.Coverage sites PA211.UserCandidate.Source.path 3947 := by
  intro i hi
  have he : i < entries.size := by rw [count_eq]; exact hi
  let e := entries[i]
  have hs : some e.site = sites[i]? := by
    have h := congrArg (fun a => a[i]?) sites_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  have hc : some e.code = PA213.SourceProgram.codes[i]? := by
    have h := congrArg (fun a => a[i]?) codes_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  refine ⟨e.code,?_,?_⟩
  · rw [candidate_resolve, ← hc]
  · have hp : PA211.UserCandidate.Source.path i = e.site.path := by simp only [PA211.UserCandidate.Source.path_eq, ← hs, Option.map_some, Option.getD_some]
    rw [hp]
    exact e.proof

#print axioms coverage
end PA211.UserCandidate.CompleteCoverage
