import PA215.Source.DestinationJoinPilot
import PA215.Contracts

namespace PA215.Source
open PA215.Runtime PA215.Contracts PA215.Zip

private theorem restart_ordinal (h : cyclicOrdinal q = some k) (r : Registers) :
    restart ⟨q,r⟩ = ⟨.at k,r⟩ := by
  cases q <;> simp_all [cyclicOrdinal, restart]

/-- The generic gluing lemma for an ORIGINAL complete primitive contract.
All finite acceptance hypotheses are decidable, and the physical reach is
strictly positive. No changed target, spare truncation, or source axiom occurs. -/
theorem checked_primitive_simulation
    (hs : exactSites[r.siteIndex]? = some s)
    (hi : resolveAt exactSites r.siteIndex = some i)
    (hp : targetPlan s r.branch = some (some p))
    (ho : instructionOutcome i r.branch = some (q,e))
    (hc : cyclicOrdinal q = some k) (hn : exactSites[k]? = some next)
    (ht : r.target = some t)
    (ha : agreesWith s r = true) (hd : destinationAgrees r = true)
    (hcheck : check fuel ⟨r.branch,r.initial,t⟩ = true)
    (n : Nat) (vs : List Nat) (hv : Valid r.branch vs) :
    cycleStep exactSites ⟨.at r.siteIndex,readFile vs⟩ =
      ⟨.at k,readFile (effectFile p.effect vs)⟩ ∧
    Reach1 PA215.NativeTable.machine (conc n vs (rootFrame s.path))
      (conc (n+p.extra) (effectFile p.effect vs) (rootFrame next.path)) := by
  have hf := destinationAgrees_frame hd hs hi hp ho hc hn
    (n+p.extra) (effectFile p.effect vs)
  constructor
  · unfold cycleStep
    rw [step_of_resolved hi, instructionOutcome_sound ho hv, restart_ordinal hc, hf.1]
  · have hrun := Contracts.sound fuel ⟨r.branch,r.initial,t⟩ hcheck n vs hv
    change Reach1 _ (conc n vs r.initial) (conc n vs t) at hrun
    rw [agrees_initial ha n vs, agrees_target ha hp ht n vs, hf.2] at hrun
    exact hrun

#print axioms checked_primitive_simulation
end PA215.Source
