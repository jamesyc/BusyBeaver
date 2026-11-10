import PA215PA.InternalModelSource
import PA215PA.InternalPhysicalFrame
import PA215PA.InternalUniformOracle
import PA215.Source.DestinationJoinPilot
namespace PA215.PA.InternalTrace.ModelSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA215.Runtime PA215.Census Symbolic PhysicalRegisters
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

private theorem restart_ordinal (q : Source.Control) (k : Nat)
    (h : Source.cyclicOrdinal q=some k) (rs : Fin 9 → V) :
    restart ⟨q,rs⟩=⟨.at k,rs⟩ := by
  cases q <;> simp_all [Source.cyclicOrdinal,restart]

/-- Exact finite source/frame bindings lift the PA-model contract theorem to
one resolved literal source instruction, including all physical file cells.
No source Nat execution is silently substituted for model execution. -/
theorem checked_primitive (r : RawOriginal) (s : Source.Site) (i : Source.Instruction)
    (p : Source.TargetPlan) (q : Source.Control) (e : Eff) (k : Nat) (next : Source.Site)
    (t : SConf) (fuel : Nat)
    (hs : Source.exactSites[r.siteIndex]?=some s)
    (hi : Source.resolveAt Source.exactSites r.siteIndex=some i)
    (hp : Source.targetPlan s r.branch=some (some p))
    (ho : Source.instructionOutcome i r.branch=some (q,e))
    (hc : Source.cyclicOrdinal q=some k) (hn : Source.exactSites[k]?=some next)
    (ht : r.target=some t) (ha : Source.agreesWith s r=true)
    (hd : Source.destinationAgrees r=true)
    (hcheck : Contracts.check fuel ⟨r.branch,r.initial,t⟩=true)
    (n xs : V) (hsize : (10 : V)≤len xs) (hg : FileBoxes.Guard xs r.branch) :
    cycleStep ⟨.at r.siteIndex,readFile xs⟩=
      ⟨.at k,readFile (FileEffects.effect p.effect xs)⟩ ∧
    Progress true (PhysicalFrame.frame s.path n xs)
      (PhysicalFrame.frame next.path (n+p.extra) (FileEffects.effect p.effect xs)) := by
  have hdest : e=p.effect ∧ sMatches (Source.rootFrame p.path) (Source.rootFrame next.path)=true := by
    simpa only [Source.destinationAgrees,hs,hi,hp,ho,hc,hn,Bool.and_eq_true,beq_iff_eq] using hd
  have hraw := ha
  simp only [Source.agreesWith,hp,ht,Bool.and_eq_true] at hraw
  have hstart := matches_config n (FileBoxes.box xs) denseControl r.initial
    (Source.rootFrame s.path) hraw.1.2
  have hend := matches_config n (FileBoxes.box xs) denseControl t
    (Source.rootFrame p.path p.extra p.effect) hraw.2.2
  have hpath : p.path.length≤64 := of_decide_eq_true hraw.2.1.2
  constructor
  · simp only [cycleStep,step,hi]
    rw [outcome_sound i r.branch q e ho xs hsize hg,restart_ordinal q k hc]
    rw [hdest.1]
  · have hrun := FileBoxes.checked_contract n xs hsize fuel
      ⟨r.branch,r.initial,t⟩ hcheck hg
    change Progress true (config n (FileBoxes.box xs) denseControl r.initial)
      (config n (FileBoxes.box xs) denseControl t) at hrun
    rw [hstart,hend,PhysicalFrame.root_effect p.path hpath p.extra p.effect n xs] at hrun
    have hnext := matches_config (n+p.extra) (FileBoxes.box (FileEffects.effect p.effect xs))
      denseControl (Source.rootFrame p.path) (Source.rootFrame next.path) hdest.2
    change Progress true (PhysicalFrame.frame s.path n xs)
      (config (n+p.extra) (FileBoxes.box (FileEffects.effect p.effect xs)) denseControl (Source.rootFrame p.path)) at hrun
    rw [hnext] at hrun
    exact hrun
end Models
#print axioms checked_primitive
end PA215.PA.InternalTrace.ModelSource
