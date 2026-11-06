import PA215.Source.InstructionOutcome
import PA215.Source.ContractJoinPilot

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source
open PA215.Runtime

/-- Control after the cyclic driver handles a normal source-root return. -/
def cyclicOrdinal : Control → Option Nat
  | .at k => some k
  | .exited => some 0
  | _ => none

/-- A stronger independent check also resolves the actual source instruction
and identifies the entire destination with its next literal source leaf. -/
def destinationAgrees (r : PA215.Census.RawOriginal) : Bool :=
  match exactSites[r.siteIndex]?, resolveAt exactSites r.siteIndex with
  | some s, some i =>
    match targetPlan s r.branch, instructionOutcome i r.branch with
    | some none, some (.halted,.none) => true
    | some (some p), some (q,e) =>
      match cyclicOrdinal q with
      | none => false
      | some k =>
        match exactSites[k]? with
        | none => false
        | some next => e == p.effect &&
            sMatches (rootFrame p.path) (rootFrame next.path)
    | _, _ => false
  | _, _ => false

/-- For IDs 0–127, resolved control-flow agrees with the frame target already
verified against the original census. -/
theorem original_first128_destinations :
    PA215.Census.C000.records.toList.all destinationAgrees = true := by decide

theorem destinationAgrees_frame (h : destinationAgrees r = true)
    (hs : exactSites[r.siteIndex]? = some s)
    (hi : resolveAt exactSites r.siteIndex = some i)
    (hp : targetPlan s r.branch = some (some p))
    (ho : instructionOutcome i r.branch = some (q,e))
    (hc : cyclicOrdinal q = some k) (hn : exactSites[k]? = some next)
    (n : Nat) (vs : List Nat) :
    e = p.effect ∧ conc n vs (rootFrame p.path) = conc n vs (rootFrame next.path) := by
  simp only [destinationAgrees, hs, hi, hp, ho, hc, hn,
    Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, sMatches_conc n vs h.2⟩

#print axioms destinationAgrees_frame
#print axioms original_first128_destinations
end PA215.Source
