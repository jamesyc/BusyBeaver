import PA215.Source.ContractJoinPilot
import PA215.Source.CensusKeys
namespace PA215.Source.ObligationKeys
attribute [local irreducible] exactSites

theorem agrees_compatible (h : agreesWith s r = true) : Compatible s.op r.branch := by
  apply compatible_of_plan
  intro hp
  simp [agreesWith,hp] at h

theorem record_compatible (h : recordAgrees r = true) :
    ∃ s, exactSites.toList[r.siteIndex]? = some s ∧ Compatible s.op r.branch := by
  unfold recordAgrees at h
  cases hs : exactSites[r.siteIndex]? with
  | none => simp [hs] at h
  | some s =>
    rw [hs] at h
    exact ⟨s,by simpa only [Array.getElem?_toList] using hs,agrees_compatible h⟩
end PA215.Source.ObligationKeys
