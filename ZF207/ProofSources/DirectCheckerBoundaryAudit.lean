module
public import DirectCtxProofRule
@[expose] public section
namespace RosserDirect.CheckerBoundaryAudit
open Turing Segment ContextProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def stopped (v : Option Symbol) (p vals scr tmp rows : List Symbol) :=
 (⟨none,v,ContextProgram.storage p vals scr tmp rows⟩ :
  TM2.Cfg (fun _ : GlobalStack => Symbol) Control (Option Symbol))

/-- Rejection is a terminal SUBROUTINE label in the current checker, not a
safe interpretation of the whole proof-race machine's halting outcome. -/
theorem reject_stops (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step ContextProgram.machine (ContextProgram.cfg .proofReject v p vals scr tmp rows) =
 some (stopped v p vals scr tmp rows) := rfl

theorem stopped_has_no_step (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step ContextProgram.machine (stopped v p vals scr tmp rows) = none := rfl

/-- Program exhaustion alone is not an acceptance signal: after a successful
canonical certificate, blindly continuing dispatch reaches a rejection label. -/
theorem exhausted_program_rejects (v : Option Symbol) (vals scr tmp rows : List Symbol) :
 TM2.step ContextProgram.machine (ContextProgram.cfg (.dispatch .start) v [] vals scr tmp rows) =
 some (ContextProgram.cfg (.dispatch .reject) none [] vals scr tmp rows) := by
 simp [ContextProgram.machine,OpcodeDispatch.machine,OpcodeDispatch.active,Routine.relocate,
   ContextProgram.cfg,TM2.step,TM2.stepAux,ContextProgram.dispatchRoles,ContextProgram.storage]

theorem exhausted_rejection_stops (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step ContextProgram.machine (ContextProgram.cfg (.dispatch .reject) v p vals scr tmp rows) =
 some (stopped v p vals scr tmp rows) := rfl

end RosserDirect.CheckerBoundaryAudit
