module

public import PA211.UserCandidate.CompleteCoverage
public import PA211.UserCandidate.Dense
public import PA211.UserCandidate.StartupProof

@[expose] public section
namespace PA211.UserCandidate.NonhaltingFromSource
open PA215.Zip PA215.Runtime PA215.Source PA211.UserCandidate.CandidateTable PA211.UserCandidate.PrimitiveSimulation PA211.UserCandidate.Source

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
    frame (PA211.UserCandidate.Source.path 68) 0 PA213.Startup.startupFile := by decide +kernel

/-- Exact binary blank execution is nonhalting whenever the unchanged literal
source is nonhalting at its actual startup register store. -/
theorem blank_nonhalting
    (h : ¬ CycleHalts exactSites ⟨.at 68,readFile PA213.Startup.startupFile⟩) :
    ¬ Halts machine PA213.Startup.blank := by
  have hs : ¬ CycleHalts sites ⟨.at 68,readFile PA213.Startup.startupFile⟩ :=
    fun hh => h ((PA211.UserCandidate.Source.cycleHalts_iff _).mp hh)
  have hv : 10 ≤ PA213.Startup.startupFile.length := by rw [PA213.Startup.startup_file_length]; decide
  have hn := PA211.UserCandidate.CompilerCorrectness.source_nonhalt_to_physical sites PA211.UserCandidate.Source.path 3947
    PA211.UserCandidate.CompleteCoverage.coverage 68 0 PA213.Startup.startupFile (by decide) hv hs
  intro hh
  have ht := halt_after_reach PA211.UserCandidate.Startup.startup_positive.reach hh
  rw [startup_frame] at ht
  exact hn ht

theorem literal_blank_nonhalting
    (h : ¬ CycleHalts exactSites ⟨.at 68,readFile PA213.Startup.startupFile⟩) :
    ¬ Halts PA211.UserCandidate.Dense.machine (zc 0 [] []) := by
  intro hh
  have hs := PA211.UserCandidate.Dense.halts_transport (c := zc 0 [] []) (by decide) hh
  exact blank_nonhalting h hs

#print axioms literal_blank_nonhalting
#print axioms blank_nonhalting
end PA211.UserCandidate.NonhaltingFromSource
