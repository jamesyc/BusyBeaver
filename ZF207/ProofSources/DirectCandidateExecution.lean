module
public import DirectCandidateDriver
public import DirectProofExecutionComplete
@[expose] public section
namespace RosserDirect.CandidateDriver
open Turing
set_option backward.isDefEq.respectTransparency false

def checkState (q : BoundaryGuard.Q) (v : Option Symbol) (p a b c r : List Symbol) : D :=
 ⟨some (.check q),v,ContextProgram.storage p a b c r⟩
theorem agree_check q (h : BoundaryGuard.machine q ≠ .halt) :
 machine (.check q) = Routine.relocate id Q.check (BoundaryGuard.machine q) := by
 cases q <;> simp_all [machine,BoundaryGuard.machine]

theorem check_run (q r : BoundaryGuard.Q) (v w : Option Symbol)
 (p a b c rows p' a' b' c' rows' : List Symbol)
 (h : TM2.Reaches BoundaryGuard.machine (BoundaryGuard.state q v p a b c rows) (BoundaryGuard.state r w p' a' b' c' rows')) :
 TM2.Reaches machine (checkState q v p a b c rows) (checkState r w p' a' b' c' rows') := by
 obtain ⟨d,hd,hr,he⟩ := Routine.lift_run id Function.injective_id Q.check BoundaryGuard.machine machine agree_check h
  (by simp [BoundaryGuard.state])
  (show Routine.Related id Q.check (BoundaryGuard.state q v p a b c rows) (checkState q v p a b c rows) from ⟨rfl,rfl,rfl⟩)
 have eq : d = checkState r w p' a' b' c' rows' := by
  rcases d with ⟨l,z,S⟩
  rcases hr with ⟨hl,hv,hs⟩
  change l = some (.check r) at hl
  change z = w at hv
  change S = ContextProgram.storage p' a' b' c' rows' at hs
  subst l; subst z; subst S
  rfl
 exact eq ▸ hd

/-- This is inference-candidate acceptance, NOT ZF-theorem acceptance. The caller
must additionally validate all context axioms and closed target, and implement
retry reset/enumeration. An assumption-row such as [⊥]⊢⊥ intentionally satisfies
this inference-only contract. -/
theorem accepts_inference_candidate (p : ZFR.Executable.Cert) (r : ZFR.Row)
 (hp : ProofInterpreter.Runs p r) (v : Option Symbol) :
 TM2.Reaches machine
 (embedded (ContextProgram.cfg (.dispatch .start) v
   (payloadBits (ZFR.TokenVM.emitCert p) ++ .frameEnd :: FramedRow.encode r) [] [] [] []))
 ⟨some .accept,none,ContextProgram.storage [] [] [] [] []⟩ := by
 have hs := hp [] v (.frameEnd :: FramedRow.encode r) []
 simp only [TypedContext.stack,List.flatMap_nil,List.append_nil] at hs
 have hm := live_run_to_return hs rfl
 have hb : TM2.Reaches machine
  (embedded (ContextProgram.cfg (.dispatch .start) none (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode r)))
  (checkState .boundary (some .frameEnd) (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode r)) :=
  Relation.ReflTransGen.single (boundary_step none (FramedRow.encode r) [] [] [] (FramedRow.encode r))
 have hc := check_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ (BoundaryGuard.accepts r (some .frameEnd))
 have he : TM2.Reaches machine (checkState .accept none [] [] [] [] [])
  ⟨some .accept,none,ContextProgram.storage [] [] [] [] []⟩ := Relation.ReflTransGen.single rfl
 exact hm.trans (hb.trans (hc.trans he))

end RosserDirect.CandidateDriver
