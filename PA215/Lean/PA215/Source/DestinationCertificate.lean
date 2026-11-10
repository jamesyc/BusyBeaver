import PA215.Source.DestinationJoinPilot
import PA215.Source.TrieResolver
namespace PA215.Source
open PA215.Runtime
attribute [local irreducible] exactSites

theorem destination_nonterminal
    (hs : exactSites[r.siteIndex]? = some s)
    (hi : resolveAt exactSites r.siteIndex = some i)
    (hp : targetPlan s r.branch = some (some p))
    (ho : instructionOutcome i r.branch = some (q,e))
    (hc : cyclicOrdinal q = some k)
    (hn : exactSites[k]? = some next)
    (hf : (e == p.effect && sMatches (rootFrame p.path) (rootFrame next.path)) = true) :
    destinationAgrees r = true := by
  simp only [destinationAgrees,hs,hi,hp,ho,hc,hn]
  exact hf

theorem destination_terminal
    (hs : exactSites[r.siteIndex]? = some s)
    (hi : resolveAt exactSites r.siteIndex = some i)
    (hp : targetPlan s r.branch = some none)
    (ho : instructionOutcome i r.branch = some (.halted,.none)) :
    destinationAgrees r = true := by
  simp only [destinationAgrees,hs,hi,hp,ho]
end PA215.Source
