import PA215.Source.CachedV2.SelectedOriginal
import PA215.Source.ResolvedContractData
import PA215.Source.FileInvariant
import PA215.Source.NonterminalPlan
import PA215.OriginalCertified
import PA215.OriginalTerminalMetadata
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PA215.Source.CachedV2
open PA215.Runtime PA215.Census PA215.Zip
attribute [local irreducible] exactSites PA215.Census.all originalAt

/-- Execution coverage only, distinct from the already proved source/census
surjectivity. The terminal original5114 is deliberately excluded. -/
def NonterminalCoverage : Prop :=
  ∀ j : Fin 5134, j.val ≠ 5114 → Nonempty (OriginalCertified j)

/-- One genuine source primitive has a strictly positive physical simulation,
including branch selection, original-ID lookup, full frames, padding and spares.
Only the two explicitly named finite certificate collections remain suppliers. -/
theorem nonhalt_primitive
    (hcoverage : NonterminalCoverage)
    (hdestinations : PA215.Census.all.toList.all destinationAgrees = true)
    (i : Nat) (s : Site) (n : Nat) (vs : List Nat)
    (hs : exactSites[i]? = some s) (hh : s.op ≠ .halt) (hv : 10 ≤ vs.length) :
    ∃ k next n' vs', exactSites[k]? = some next ∧ 10 ≤ vs'.length ∧
      cycleStep exactSites ⟨.at i,readFile vs⟩ = ⟨.at k,readFile vs'⟩ ∧
      Reach1 PA215.NativeTable.machine (conc n vs (rootFrame s.path))
        (conc n' vs' (rootFrame next.path)) := by
  obtain ⟨j,hj,hvalid,ha⟩ := selected_original i s vs hs hv
  obtain ⟨target,ht⟩ := nonhalt_original_target ha hh
  have hjne : j.val ≠ 5114 := by
    intro he
    have hn := (originalAt_target_none_iff j).mpr he
    rw [ht] at hn
    cases hn
  obtain ⟨cert⟩ := hcoverage j hjne
  have hd : destinationAgrees (originalAt j) = true :=
    (List.all_eq_true.mp hdestinations) _ (originalAt_mem j)
  have hsource : exactSites[(originalAt j).siteIndex]? = some s := by rw [hj]; exact hs
  obtain ⟨inst,p,q,e,k,next,hi,hp,ho,hc,hn⟩ :=
    resolved_nonterminal_data hsource ha cert.target_eq hd
  have hsim := checked_primitive_simulation hsource hi hp ho hc hn cert.target_eq
    ha hd cert.accepted n vs hvalid
  rw [hj] at hsim
  exact ⟨k,next,n+p.extra,effectFile p.effect vs,hn,
    effectFile_valid_length p.effect vs hv,hsim.1,hsim.2⟩
#print axioms nonhalt_primitive
end PA215.Source.CachedV2
