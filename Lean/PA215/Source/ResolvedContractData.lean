import PA215.Source.PrimitiveSimulation
namespace PA215.Source
open PA215.Runtime
attribute [local irreducible] exactSites

/-- Recover every semantic supplier from the two concrete comparison Booleans
and a nonterminal original target. No destination is selected by trust. -/
theorem resolved_nonterminal_data
    (hs : exactSites[r.siteIndex]? = some s)
    (ha : agreesWith s r = true) (ht : r.target = some t)
    (hd : destinationAgrees r = true) :
    ∃ i p q e k next,
      resolveAt exactSites r.siteIndex = some i ∧
      targetPlan s r.branch = some (some p) ∧
      instructionOutcome i r.branch = some (q,e) ∧
      cyclicOrdinal q = some k ∧ exactSites[k]? = some next := by
  cases hp : targetPlan s r.branch with
  | none => simp [agreesWith,hp] at ha
  | some po =>
    cases po with
    | none => simp [agreesWith,hp,ht] at ha
    | some p =>
      cases hi : resolveAt exactSites r.siteIndex with
      | none => simp [destinationAgrees,hs,hi] at hd
      | some i =>
        cases ho : instructionOutcome i r.branch with
        | none => simp [destinationAgrees,hs,hi,hp,ho] at hd
        | some qe =>
          rcases qe with ⟨q,e⟩
          cases hc : cyclicOrdinal q with
          | none => simp [destinationAgrees,hs,hi,hp,ho,hc] at hd
          | some k =>
            cases hn : exactSites[k]? with
            | none => simp [destinationAgrees,hs,hi,hp,ho,hc,hn] at hd
            | some next => exact ⟨i,p,q,e,k,next,rfl,rfl,ho,hc,hn⟩

#print axioms resolved_nonterminal_data
end PA215.Source
