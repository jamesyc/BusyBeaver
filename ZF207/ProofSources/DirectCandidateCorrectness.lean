module
public import DirectCandidateSoundness
public import DirectCanonicalComplete
@[expose] public section
namespace RosserDirect.CandidateDriver
open Turing
set_option backward.isDefEq.respectTransparency false
/-- Unconditional exact equivalence for every canonical inference certificate.
No arbitrary-stream parser soundness or ZF context validation is claimed. -/
theorem accepts_iff (p : ZFR.Executable.Cert) (r : ZFR.Row) :
 TM2.Reaches machine (initial p r) accepted ↔ ZFR.Executable.conclusion p = some r := by
 constructor
 · exact canonical_acceptance p r (ProofInterpreter.evaluates_all p)
 · intro h
   have hp := ProofInterpreter.evaluates_all p
   cases hc : ZFR.Executable.check p with
   | none => simp [ZFR.Executable.conclusion,hc] at h
   | some q =>
     have eq : q.val = r := by simpa [ZFR.Executable.conclusion,hc] using h
     have hr : ProofInterpreter.Runs p q.val := by simpa [ProofInterpreter.Evaluates,hc] using hp
     exact accepts_inference_candidate p r (eq ▸ hr) none

end RosserDirect.CandidateDriver
