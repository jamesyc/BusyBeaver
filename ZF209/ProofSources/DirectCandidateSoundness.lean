module
public import DirectCandidateExecution
public import DirectCanonicalEvaluation
@[expose] public section
namespace RosserDirect.CandidateDriver
open Turing
set_option backward.isDefEq.respectTransparency false

def initial (p : ZFR.Executable.Cert) (r : ZFR.Row) : D :=
 embedded (ContextProgram.cfg (.dispatch .start) none
  (payloadBits (ZFR.TokenVM.emitCert p) ++ .frameEnd :: FramedRow.encode r) [] [] [] [])
def accepted : D := ⟨some .accept,none,ContextProgram.storage [] [] [] [] []⟩
def retryState (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) : D := ⟨some .retry,v,S⟩

theorem retry_reaches (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) {d : D}
 (h : TM2.Reaches machine (retryState v S) d) : d = retryState v S := by
 induction h with
 | refl => rfl
 | @tail b c h hs ih =>
   rw [ih] at hs
   exact Option.some.inj (hs.symm.trans (retry_live v S))

theorem acceptance_cannot_retry (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) :
 ¬ TM2.Reaches machine accepted (retryState v S) := by
 intro h
 rcases Relation.ReflTransGen.cases_head h with eq | ⟨b,hb,hbr⟩
 · have he := congrArg TM2.Cfg.l eq
   simp [accepted,retryState] at he
 · have step : TM2.step machine accepted = some ⟨none,none,ContextProgram.storage [] [] [] [] []⟩ := rfl
   have eq : b = ⟨none,none,ContextProgram.storage [] [] [] [] []⟩ := Option.some.inj (hb.symm.trans step)
   subst b
   have he := congrArg TM2.Cfg.l (Routine.dead_reaches machine rfl hbr)
   simp [retryState] at he

theorem retry_excludes_acceptance {c : D} (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol)
 (hr : TM2.Reaches machine c (retryState v S)) : ¬TM2.Reaches machine c accepted := by
 intro ha
 have hu : Relator.RightUnique (fun a b : D => TM2.step machine a = some b) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)
 rcases Relation.ReflTransGen.total_of_right_unique hu hr ha with h | h
 · have he := congrArg TM2.Cfg.l (retry_reaches v S h)
   simp [accepted,retryState] at he
 · exact acceptance_cannot_retry v S h

theorem rejected_candidate_retries (p : ZFR.Executable.Cert) (r : ZFR.Row)
 (hp : ProofInterpreter.Rejects p) :
 ∃ v S, TM2.Reaches machine (initial p r) (retryState v S) := by
 obtain ⟨v,pr,a,b,c,rows,h⟩ := hp [] none (.frameEnd :: FramedRow.encode r) []
 simp only [TypedContext.stack,List.flatMap_nil,List.append_nil] at h
 have hh := live_run_to_reject h rfl
 have hs : TM2.Reaches machine (embedded (ContextProgram.cfg .proofReject v pr a b c rows))
  (retryState v (ContextProgram.storage pr a b c rows)) := Relation.ReflTransGen.single (rejection_to_retry v pr a b c rows)
 exact ⟨v,_,hh.trans hs⟩

theorem mismatched_candidate_retries (p : ZFR.Executable.Cert) (expected actual : ZFR.Row)
 (hp : ProofInterpreter.Runs p actual) (hne : expected ≠ actual) :
 ∃ v S, TM2.Reaches machine (initial p expected) (retryState v S) := by
 have h := hp [] none (.frameEnd :: FramedRow.encode expected) []
 simp only [TypedContext.stack,List.flatMap_nil,List.append_nil] at h
 have hm := live_run_to_return h rfl
 have hb : TM2.Reaches machine
  (embedded (ContextProgram.cfg (.dispatch .start) none (.frameEnd :: FramedRow.encode expected) [] [] [] (FramedRow.encode actual)))
  (checkState .boundary (some .frameEnd) (.frameEnd :: FramedRow.encode expected) [] [] [] (FramedRow.encode actual)) :=
  Relation.ReflTransGen.single (boundary_step none (FramedRow.encode expected) [] [] [] (FramedRow.encode actual))
 obtain ⟨v,left,right,hg⟩ := BoundaryGuard.rejects_wrong_row expected actual hne (some .frameEnd)
 have hc := check_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg
 have he : TM2.Reaches machine (checkState .reject v [] [] [] left right)
  (retryState v (ContextProgram.storage [] [] [] left right)) := Relation.ReflTransGen.single rfl
 exact ⟨v,_,hm.trans (hb.trans (hc.trans he))⟩

/-- Actual wrapped-driver acceptance soundness for a canonical certificate.
The only structural evaluation premise must be discharged for every constructor
before claiming a general canonical checker theorem. ZF axiom/closed-target
validation and enumeration are separate obligations. -/
theorem canonical_acceptance (p : ZFR.Executable.Cert) (r : ZFR.Row)
 (hp : ProofInterpreter.Evaluates p) (ha : TM2.Reaches machine (initial p r) accepted) :
 ZFR.Executable.conclusion p = some r := by
 cases h : ZFR.Executable.check p with
 | none =>
   have hr : ProofInterpreter.Rejects p := by simpa [ProofInterpreter.Evaluates,h] using hp
   obtain ⟨v,S,hh⟩ := rejected_candidate_retries p r hr
   exact False.elim (retry_excludes_acceptance v S hh ha)
 | some q =>
   have hr : ProofInterpreter.Runs p q.val := by simpa [ProofInterpreter.Evaluates,h] using hp
   have eq : r = q.val := by
    by_contra hn
    obtain ⟨v,S,hh⟩ := mismatched_candidate_retries p r q.val hr hn
    exact retry_excludes_acceptance v S hh ha
   simp [ZFR.Executable.conclusion,h,eq]
end RosserDirect.CandidateDriver
