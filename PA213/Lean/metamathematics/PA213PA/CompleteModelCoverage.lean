import PA213PA.ModelCoverage
import PA213.SourceEquivalence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.PA.CompleteModelCoverage
open PA215.Source PA213.SourceProgram PA213.SourceEquivalence PA213.PA.ModelPrimitive PA213.PA.ModelCoverage

theorem coverage : ∀ i, i<3947 → ∃ code,
    resolveAt exactSites i=some code ∧ Implements PA213.FastPaths.path 3947 (PA213.FastPaths.path i) code := by
  intro i hi
  have he : i < entries.size := by rw [count_eq]; exact hi
  let e := entries[i]
  have hs : some e.site = sites[i]? := by
    have h := congrArg (fun a => a[i]?) sites_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  have hc : some e.code = codes[i]? := by
    have h := congrArg (fun a => a[i]?) codes_eq
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem he, Option.map_some] using h
  refine ⟨e.code,?_,?_⟩
  · rw [baseline_resolve, ← hc]
  · have hp : PA213.FastPaths.path i = e.site.path := by simp only [PA213.FastPaths.path_eq,path, ← hs, Option.map_some, Option.getD_some]
    rw [hp]
    exact @e.proof

#print axioms coverage
end PA213.PA.CompleteModelCoverage
