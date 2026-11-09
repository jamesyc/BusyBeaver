/- Minimized211 candidate: fresh arithmetic/native model runtime.
The unchanged original source interpreter is reused explicitly. -/
import User211PANativeTable
import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA211.UserCandidate.InternalCallAudit
open PA215.Runtime
/-- Audit only the box oracle calls visited before the original exec target test.
A true audit is not an execution theorem. Arithmetic model soundness is separate. -/
def localAllowed (allowed : Nat → BoxSt → Bool) (br : Branch) : SConf → Bool
  | (q,false,_,[.box x]) =>
      match oracle q br x with
      | none => true
      | some _ => allowed q x
  | _ => true

def check (allowed : Nat → BoxSt → Bool) (br : Branch) (tgt : SConf → Bool) :
    Nat → SConf → Bool → Bool
  | 0,_,_ => true
  | f+1,s,moved =>
      if moved && tgt s then true
      else match sstep PA211.UserCandidate.NativeTable.machine br s with
        | none => true
        | some (s',m) => localAllowed allowed br s && check allowed br tgt f s' (moved || m)

end PA211.UserCandidate.InternalCallAudit
