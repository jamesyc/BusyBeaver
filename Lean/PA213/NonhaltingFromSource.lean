import PA213.CompleteCoverage
import PA213.StartupProof
namespace PA213.NonhaltingFromSource
open PA215.Zip PA215.Runtime PA215.Source PA213.CandidateTable PA213.PrimitiveSimulation PA213.SourceProgram

/-- Determinism transports any alleged halt beyond a known finite prefix. -/
private theorem halt_after_reach {M : TMN} {a b : Conf} (hr : Reach M a b) (hh : Halts M a) : Halts M b := by
  obtain ⟨n,hn⟩ := hr
  obtain ⟨z,⟨k,hk⟩,hz⟩ := hh
  by_cases hnk : n ≤ k
  · refine ⟨z,⟨k-n,?_⟩,hz⟩
    have he : k = n + (k-n) := by omega
    rw [he,run_add,hn] at hk
    exact hk
  · have he : n = k + (n-k) := by omega
    have hp : 0 < n-k := by omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-k ≠ 0)
    rw [he,run_add,hk,hm] at hn
    simp [PA215.Zip.run,hz] at hn

theorem startup_frame : PA213.Startup.startupTarget =
    frame (PA213.FastPaths.path 68) 0 PA213.Startup.startupFile := by decide +kernel

/-- Exact binary blank execution is nonhalting whenever the unchanged literal
source is nonhalting at its actual startup register store. -/
theorem blank_nonhalting
    (h : ¬ CycleHalts exactSites ⟨.at 68,readFile PA213.Startup.startupFile⟩) :
    ¬ Halts machine PA213.Startup.blank := by
  have hs : ¬ CycleHalts sites ⟨.at 68,readFile PA213.Startup.startupFile⟩ :=
    fun hh => h ((PA213.SourceEquivalence.cycleHalts_iff _).mp hh)
  have hv : 10 ≤ PA213.Startup.startupFile.length := by rw [PA213.Startup.startup_file_length]; decide
  have hn := PA213.CompilerCorrectness.source_nonhalt_to_physical sites PA213.FastPaths.path 3947
    PA213.CompleteCoverage.coverage 68 0 PA213.Startup.startupFile (by decide) hv hs
  intro hh
  have ht := halt_after_reach PA213.Startup.startup_positive.reach hh
  rw [startup_frame] at ht
  exact hn ht

#print axioms blank_nonhalting
end PA213.NonhaltingFromSource
