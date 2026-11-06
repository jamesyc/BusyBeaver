import PA215PA.InternalSourceCoverage
import PA215PA.InternalTerminalContract
import PA215.Source.CachedV2.TerminalPrimitive
set_option maxRecDepth 100000
namespace PA215.PA.InternalTrace.ModelSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA215.Runtime PA215.Census Symbolic PhysicalRegisters
attribute [local irreducible] Source.exactSites PA215.Census.all originalAt
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Every actual literal halt leaf reaches dense halt215 in every PA model.
This is a single fixed-control instruction theorem, not a nonstandard-length
source execution induction. Full physical file and padding are retained. -/
theorem halt_primitive (i : Nat) (s : Source.Site) (n xs : V)
    (hs : Source.exactSites[i]?=some s) (hh : s.op=.halt) (hsize : (10 : V)≤len xs) :
    ∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs
      (PhysicalFrame.frame s.path n xs).q
      (PhysicalFrame.frame s.path n xs).left
      (PhysicalFrame.frame s.path n xs).right 215 lf rf := by
  obtain ⟨j,hj,hg,ha⟩ := selected_original i s xs hs
  have ht := Source.CachedV2.halt_original_target ha hh
  have he : j=(⟨5114,by decide⟩ : Fin 5134) :=
    Fin.ext ((originalAt_target_none_iff j).mp ht)
  subst j
  let cert := AllRuntimeCertificates.terminalCertificate
  have hrun := FileBoxes.checked_halt n xs hsize cert.fuel _ _ cert.accepted hg
  have hraw := ha
  simp only [Source.agreesWith,Bool.and_eq_true] at hraw
  have hstart := matches_config n (FileBoxes.box xs) denseControl _ _ hraw.1.2
  change config n (FileBoxes.box xs) denseControl _=PhysicalFrame.frame s.path n xs at hstart
  rw [hstart] at hrun
  exact hrun
end Models
#print axioms halt_primitive
end PA215.PA.InternalTrace.ModelSource
