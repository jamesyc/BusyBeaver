module
public import DirectCanonicalEvaluation
public import DirectCheckerBoundaryAudit
public import ExecutableZFProof
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR CheckerBoundaryAudit
set_option backward.isDefEq.respectTransparency false
abbrev State := TM2.Cfg (fun _ : GlobalStack => Symbol) Control (Option Symbol)

def finished (r : Row) : State :=
 ContextProgram.cfg (.dispatch .start) none [] [] [] [] (FramedRow.encode r)

theorem dead_reaches {a b : State} (hs : TM2.step ContextProgram.machine a = none)
 (h : TM2.Reaches ContextProgram.machine a b) : a = b := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨c,hc,_⟩
 · exact he
 · simp [hs] at hc

theorem one_reaches {a d b : State} (hs : TM2.step ContextProgram.machine a = some d)
 (hd : TM2.step ContextProgram.machine d = none)
 (h : TM2.Reaches ContextProgram.machine a b) : b = a ∨ b = d := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨c,hc,hcb⟩
 · exact Or.inl he.symm
 · have hc' : c = d := Option.some.inj (hc.symm.trans hs)
   subst c
   exact Or.inr (dead_reaches hd hcb).symm

theorem finished_reaches {r : Row} {b : State}
 (h : TM2.Reaches ContextProgram.machine (finished r) b) :
 b = finished r ∨
 b = ContextProgram.cfg (.dispatch .reject) none [] [] [] [] (FramedRow.encode r) ∨
 b = stopped none [] [] [] [] (FramedRow.encode r) := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨c,hc,hcb⟩
 · exact Or.inl he.symm
 · have hs := exhausted_program_rejects none [] [] [] (FramedRow.encode r)
   have hc' : c = ContextProgram.cfg (.dispatch .reject) none [] [] [] [] (FramedRow.encode r) :=
     Option.some.inj (hc.symm.trans hs)
   subst c
   exact Or.inr (one_reaches (exhausted_rejection_stops _ _ _ _ _ _)
     (stopped_has_no_step _ _ _ _ _ _) hcb)

theorem rejects_not_finished {p : Executable.Cert} (hp : Rejects p) (r : Row) :
 ¬ TM2.Reaches ContextProgram.machine
   (ContextProgram.cfg (.dispatch .start) none (payloadBits (TokenVM.emitCert p)) [] [] [] [])
   (finished r) := by
 intro h
 obtain ⟨w,program,vals,scratch,tmp,out,hr⟩ := hp [] none [] []
 simp only [TypedContext.stack,List.append_nil] at hr
 have hu : Relator.RightUnique (fun a b : State => TM2.step ContextProgram.machine a = some b) := by
   intro a b c hab hac
   exact Option.some.inj (hab.symm.trans hac)
 rcases Relation.ReflTransGen.total_of_right_unique hu hr h with hj | hj
 · rcases one_reaches (reject_stops _ _ _ _ _ _) (stopped_has_no_step _ _ _ _ _ _) hj with he | he
   · have := congrArg TM2.Cfg.l he; simp [finished,ContextProgram.cfg] at this
   · have := congrArg TM2.Cfg.l he; simp [finished,stopped,ContextProgram.cfg] at this
 · rcases finished_reaches hj with he | he | he
   all_goals have := congrArg TM2.Cfg.l he
   all_goals simp [finished,stopped,ContextProgram.cfg] at this

theorem runs_finished_unique {p : Executable.Cert} {r q : Row}
 (hp : Runs p r)
 (h : TM2.Reaches ContextProgram.machine
   (ContextProgram.cfg (.dispatch .start) none (payloadBits (TokenVM.emitCert p)) [] [] [] [])
   (finished q)) : r = q := by
 have hr := hp [] none [] []
 simp only [TypedContext.stack,List.append_nil] at hr
 have hu : Relator.RightUnique (fun a b : State => TM2.step ContextProgram.machine a = some b) := by
   intro a b c hab hac
   exact Option.some.inj (hab.symm.trans hac)
 have eq : finished r = finished q := by
   rcases Relation.ReflTransGen.total_of_right_unique hu hr h with hj | hj
   · rcases finished_reaches hj with he | he | he
     · exact he.symm
     all_goals have := congrArg TM2.Cfg.l he
     all_goals simp [finished,stopped,ContextProgram.cfg] at this
   · rcases finished_reaches hj with he | he | he
     · exact he
     all_goals have := congrArg TM2.Cfg.l he
     all_goals simp [finished,stopped,ContextProgram.cfg] at this
 apply FramedRow.encode_injective
 exact congrArg (fun c : State => c.stk GlobalStack.rows) eq

/-- Actual execution soundness conditional only on the structural evaluation
lemma for this canonical certificate. The final row and all residual stacks are
exact, and the input is exhausted. -/
theorem canonical_acceptance {p : Executable.Cert} (hp : Evaluates p) (r : Row)
 (h : TM2.Reaches ContextProgram.machine
   (ContextProgram.cfg (.dispatch .start) none (payloadBits (TokenVM.emitCert p)) [] [] [] [])
   (finished r)) : Executable.conclusion p = some r := by
 cases hc : Executable.check p with
 | none => exact False.elim (rejects_not_finished (by simpa [Evaluates,hc] using hp) r h)
 | some q =>
   have he := runs_finished_unique (by simpa [Evaluates,hc] using hp : Runs p q.val) h
   simp [Executable.conclusion,hc,he]

end RosserDirect.ProofInterpreter
