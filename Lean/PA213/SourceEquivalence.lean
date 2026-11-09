module

public import PA213.AllSourceChecks
public import PA215.Source.CyclicDeterminism

@[expose] public section
namespace PA213.SourceEquivalence
open PA215.Source PA215.Source.PathTrie PA213.FastResolve PA213.SourceProgram

theorem candidate_resolve (i : Nat) : resolveAt sites i = codes[i]? := by
  by_cases hi : i < 3947
  · rw [PA213.SourceCheck.resolve_eq_tree sites trie flatten_exact]
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (PA213.AllSourceChecks.checked i hi)).1).1
  · have hs : sites[i]? = none := Array.getElem?_eq_none_iff.mpr (by rw [sites_count]; omega)
    have hc : codes[i]? = none := Array.getElem?_eq_none_iff.mpr (by rw [codes_count]; omega)
    simp [resolveAt,hs,hc]

theorem baseline_resolve (i : Nat) : resolveAt exactSites i = codes[i]? := by
  by_cases hi : i < 3947
  · rw [PA213.SourceCheck.resolve_eq_tree exactSites exactTrie exact_flatten]
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (PA213.AllSourceChecks.checked i hi)).1).2
  · have hs : exactSites[i]? = none := Array.getElem?_eq_none_iff.mpr (by rw [exactSites_count]; omega)
    have hc : codes[i]? = none := Array.getElem?_eq_none_iff.mpr (by rw [codes_count]; omega)
    simp [resolveAt,hs,hc]

theorem resolve_eq (i : Nat) : resolveAt sites i = resolveAt exactSites i := by
  rw [candidate_resolve,baseline_resolve]

theorem step_eq (c : Configuration) : step sites c = step exactSites c := by
  rcases c with ⟨q,r⟩
  cases q <;> simp only [step,resolve_eq]

theorem cycleStep_eq (c : Configuration) : cycleStep sites c = cycleStep exactSites c := by
  simp only [cycleStep,step_eq]

theorem cycleRun_eq (n : Nat) (c : Configuration) : cycleRun sites n c = cycleRun exactSites n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [cycleRun,cycleStep_eq,ih]

theorem cycleHalts_iff (c : Configuration) : CycleHalts sites c ↔ CycleHalts exactSites c := by
  simp only [CycleHalts,cycleRun_eq]

theorem path_short (i : Nat) : (path i).length ≤ 64 := by
  by_cases hi : i < 3947
  · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (PA213.AllSourceChecks.checked i hi)).2
  · have hs : sites[i]? = none := Array.getElem?_eq_none_iff.mpr (by rw [sites_count]; omega)
    simp [path,hs]

#print axioms cycleHalts_iff
end PA213.SourceEquivalence
