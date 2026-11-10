import PA215.ContractPilot
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.InternalCallAudit
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
      else match sstep NativeTable.machine br s with
        | none => true
        | some (s',m) => localAllowed allowed br s && check allowed br tgt f s' (moved || m)

def calls5 (q : Nat) (x : BoxSt) : Bool :=
  (q == 36 && x == .plain .none) || (q == 64 && x == .mark 1)

theorem certificate5_calls :
    check calls5 ContractPilot.c5.branch
      (fun s => sMatches s ContractPilot.c5.target) 4000 ContractPilot.c5.initial false=true := by
  decide
#print axioms certificate5_calls
end PA215.InternalCallAudit
