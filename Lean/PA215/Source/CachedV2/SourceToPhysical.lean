import PA215.Source.CachedV2.GlobalPrimitive
import PA215.Source.CyclicDeterminism
import PA215.PositiveInvariant
set_option maxRecDepth 100000
namespace PA215.Source.CachedV2
open PA215.Runtime PA215.Zip
attribute [local irreducible] exactSites

theorem nonhalting_source_op (hs : exactSites[i]? = some s)
    (hno : ¬ CycleHalts exactSites ⟨.at i,regs⟩) : s.op ≠ .halt := by
  intro hh
  have hi : resolveAt exactSites i = some .halt := by
    unfold resolveAt
    rw [hs]
    simp [resolve,hh]
  apply hno
  refine ⟨1,?_⟩
  change (restart (step exactSites ⟨.at i,regs⟩)).control = .halted
  rw [step_of_resolved hi]
  rfl

def SafePhysicalFrame (c : PA215.Zip.Conf) : Prop :=
  ∃ i s n vs, exactSites[i]? = some s ∧ 10 ≤ vs.length ∧
    ¬ CycleHalts exactSites ⟨.at i,readFile vs⟩ ∧ c = conc n vs (rootFrame s.path)

theorem safe_frame_progress
    (hcoverage : NonterminalCoverage)
    (hdestinations : PA215.Census.all.toList.all destinationAgrees = true)
    (c : PA215.Zip.Conf) (hc : SafePhysicalFrame c) :
    ∃ d, Reach1 PA215.NativeTable.machine c d ∧ SafePhysicalFrame d := by
  obtain ⟨i,s,n,vs,hs,hv,hno,rfl⟩ := hc
  have hh := nonhalting_source_op hs hno
  obtain ⟨k,next,n',vs',hn,hv',hstep,hmove⟩ :=
    nonhalt_primitive hcoverage hdestinations i s n vs hs hh hv
  refine ⟨conc n' vs' (rootFrame next.path),hmove,k,next,n',vs',hn,hv',?_,rfl⟩
  rintro ⟨m,hm⟩
  apply hno
  refine ⟨m+1,?_⟩
  simpa only [cycleRun,hstep] using hm

/-- Physical nonhalting follows from source nonhalting, coverage of nonterminal records, and agreement of their destinations. Positive progress preserves the simulation invariant. -/
theorem source_nonhalt_to_physical
    (hcoverage : NonterminalCoverage)
    (hdestinations : PA215.Census.all.toList.all destinationAgrees = true)
    (hs : exactSites[i]? = some s) (hv : 10 ≤ vs.length)
    (hno : ¬ CycleHalts exactSites ⟨.at i,readFile vs⟩) (n : Nat) :
    ¬ PA215.Zip.Halts PA215.NativeTable.machine (conc n vs (rootFrame s.path)) := by
  apply PA215.Zip.not_halts_of_positive_invariant PA215.NativeTable.machine SafePhysicalFrame
    (safe_frame_progress hcoverage hdestinations)
  exact ⟨i,s,n,vs,hs,hv,hno,rfl⟩
#print axioms source_nonhalt_to_physical
end PA215.Source.CachedV2
