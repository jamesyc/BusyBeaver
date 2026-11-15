module
public import DirectClosedTargetGate
public import DirectWitnessContextCheck
public import DirectCandidateCorrectness
@[expose] public section
namespace RosserDirect.ZFDriver
open Turing
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | scope (q : ClosedTargetGate.Q) | context (q : WitnessContextCheck.Q) | infer (q : CandidateDriver.Q) | retry | accept
 deriving DecidableEq, Fintype, Inhabited
abbrev D := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
abbrev S := TM2.Stmt (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
def roles : FourStack.K → ContextProgram.GlobalStack
 | .stream => .program | .data => .values | .scratch => .scratch | .output => .temporary
theorem roles_injective : Function.Injective roles := by intro a b h; cases a <;> cases b <;> simp_all [roles]
def machine : Q → S
 | .scope .accept => .goto (fun _ => .context (.uncons .tag0))
 | .scope .reject => .goto (fun _ => .retry)
 | .scope q => Routine.relocate roles Q.scope (ClosedTargetGate.machine q)
 | .context .accept => .load (fun _ => none) (.goto (fun _ => .infer (.run (.dispatch .start))))
 | .context .reject => .goto (fun _ => .retry)
 | .context q => Routine.relocate id Q.context (WitnessContextCheck.machine q)
 | .infer .accept => .goto (fun _ => .accept)
 | .infer .retry => .goto (fun _ => .retry)
 | .infer q => Routine.relocate id Q.infer (CandidateDriver.machine q)
 | .retry => .goto (fun _ => .retry)
 | .accept => .halt

def state (q : Q) (v : Option Symbol) (p a b c rows : List Symbol) : D :=
 ⟨some q,v,ContextProgram.storage p a b c rows⟩
def embedded (c : CandidateDriver.D) : D := ⟨c.l.map Q.infer,c.var,c.stk⟩
def tail (p : ZFR.Executable.Cert) (Γ : ZFR.Context) (f : ZFR.Formula) : List Symbol :=
 payloadBits (ZFR.TokenVM.emitCert p) ++ .frameEnd :: FramedRow.encode (.seq Γ f)
def initial (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert) (Γ : ZFR.Context) (f : ZFR.Formula) : D :=
 state (.scope (.save .scan)) none (WitnessContextCheck.codes ws ++ .frameEnd :: tail p Γ f)
  (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ)) [] [] []
def accepted : D := state .accept none [] [] [] [] []

theorem agree_scope q (h : ClosedTargetGate.machine q ≠ .halt) :
 machine (.scope q) = Routine.relocate roles Q.scope (ClosedTargetGate.machine q) := by
 cases q <;> simp_all [machine,ClosedTargetGate.machine]
theorem embed_scope q v (p a b c rows : List Symbol) :
 FourStack.embed4 roles Q.scope (FourStack.cfg4 q v p a b c) (fun _ => rows) = state (.scope q) v p a b c rows := by
 unfold FourStack.embed4 FourStack.cfg4 state
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl

theorem scope_run q r v w p a b c p' a' b' c' (rows : List Symbol)
 (h : TM2.Reaches ClosedTargetGate.machine (FourStack.cfg4 q v p a b c) (FourStack.cfg4 r w p' a' b' c')) :
 TM2.Reaches machine (state (.scope q) v p a b c rows) (state (.scope r) w p' a' b' c' rows) := by
 have hh := FourStack.lift4_run roles roles_injective Q.scope ClosedTargetGate.machine machine agree_scope (fun _ => rows) h (by simp [FourStack.cfg4])
 simpa only [embed_scope] using hh

/-- The inference driver's retry label is redirected to the outer retry label.
Only traces ending before execution of retry are embedded here. -/
theorem infer_stepAux (s : TM2.Stmt (fun _ : ContextProgram.GlobalStack => Symbol) CandidateDriver.Q (Option Symbol)) v S :
 TM2.stepAux (Routine.relocate id Q.infer s) v S = embedded (TM2.stepAux s v S) := by
 have h := Routine.relocate_correct id Function.injective_id Q.infer s v S S rfl
 generalize ha : TM2.stepAux s v S = a at h ⊢
 generalize hb : TM2.stepAux (Routine.relocate id Q.infer s) v S = b at h ⊢
 rcases a with ⟨l,w,T⟩
 rcases b with ⟨l',w',T'⟩
 rcases h with ⟨hl,hv,hs⟩
 change l' = l.map Q.infer at hl
 change w' = w at hv
 change T' = T at hs
 subst l'; subst w'; subst T'
 rfl

/-- A trace that reaches accept cannot pass through retry, which is a self-loop.
This makes successful inference traces compatible with outer retry routing. -/
theorem infer_run_accept {c : CandidateDriver.D} (h : TM2.Reaches CandidateDriver.machine c CandidateDriver.accepted) :
 TM2.Reaches machine (embedded c) (embedded CandidateDriver.accepted) := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | @head a b hab hba ih =>
   have live : b.l ≠ none := Routine.source_live CandidateDriver.machine hba (by simp [CandidateDriver.accepted])
   have hn : a.l ≠ some .retry := by
    intro he
    rcases a with ⟨l,v,S⟩
    change l = some .retry at he
    subst l
    have eq : b = CandidateDriver.retryState v S := Option.some.inj (hab.symm.trans (CandidateDriver.retry_live v S))
    subst b
    have he := congrArg TM2.Cfg.l (CandidateDriver.retry_reaches v S hba)
    simp [CandidateDriver.accepted,CandidateDriver.retryState] at he
   have ha : a.l ≠ some .accept := by
    intro he
    rcases a with ⟨l,v,S⟩
    change l = some .accept at he
    subst l
    have hd : b = ⟨none,v,S⟩ := Option.some.inj (hab.symm.trans rfl)
    exact live (hd ▸ rfl)
   rcases a with ⟨l,v,S⟩
   cases l with
   | none => simp [TM2.step] at hab
   | some q =>
     have hq : q ≠ .retry ∧ q ≠ .accept := by simpa using And.intro hn ha
     have hd : b = TM2.stepAux (CandidateDriver.machine q) v S := by simpa [TM2.step] using hab.symm
     have hs : TM2.step machine (embedded ⟨some q,v,S⟩) = some (embedded b) := by
      rw [hd]
      cases q <;> simp_all [machine,embedded,TM2.step,infer_stepAux]
     have step : TM2.Reaches machine (embedded ⟨some q,v,S⟩) (embedded b) := Relation.ReflTransGen.single hs
     exact step.trans ih

theorem agree_context q (h : WitnessContextCheck.machine q ≠ .halt) :
 machine (.context q) = Routine.relocate id Q.context (WitnessContextCheck.machine q) := by
 cases q <;> simp_all [machine,WitnessContextCheck.machine]

theorem context_run q r v w p a b c rows p' a' b' c' rows'
 (h : TM2.Reaches WitnessContextCheck.machine (WitnessContextCheck.cfg q v p a b c rows) (WitnessContextCheck.cfg r w p' a' b' c' rows')) :
 TM2.Reaches machine (state (.context q) v p a b c rows) (state (.context r) w p' a' b' c' rows') := by
 obtain ⟨d,hd,hr,he⟩ := Routine.lift_run id Function.injective_id Q.context WitnessContextCheck.machine machine agree_context h
  (by simp [WitnessContextCheck.cfg])
  (show Routine.Related id Q.context (WitnessContextCheck.cfg q v p a b c rows) (state (.context q) v p a b c rows) from ⟨rfl,rfl,rfl⟩)
 have eq : d = state (.context r) w p' a' b' c' rows' := by
  rcases d with ⟨l,z,S⟩
  rcases hr with ⟨hl,hv,hs⟩
  change l = some (.context r) at hl
  change z = w at hv
  change S = ContextProgram.storage p' a' b' c' rows' at hs
  subst l; subst z; subst S
  rfl
 exact eq ▸ hd

theorem scope_to_context (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert)
 (Γ : ZFR.Context) (f : ZFR.Formula) (hf : ZFR.Bound f 0) :
 TM2.Reaches machine (initial ws p Γ f)
 (state (.context (.uncons .tag0)) none (WitnessContextCheck.codes ws ++ .frameEnd::tail p Γ f)
  (TypedContext.value (.context Γ)) [] [] []) := by
 have h := scope_run _ _ _ _ _ _ _ _ _ _ _ _ []
  (ClosedTargetGate.accepts f hf none (WitnessContextCheck.codes ws ++ .frameEnd::tail p Γ f) (TypedContext.value (.context Γ)) [])
 have he : TM2.Reaches machine
  (state (.scope .accept) none (WitnessContextCheck.codes ws ++ .frameEnd::tail p Γ f) (TypedContext.value (.context Γ)) [] [] [])
  (state (.context (.uncons .tag0)) none (WitnessContextCheck.codes ws ++ .frameEnd::tail p Γ f) (TypedContext.value (.context Γ)) [] [] []) := Relation.ReflTransGen.single rfl
 exact h.trans he

theorem gates_to_inference (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert)
 (Γ : ZFR.Context) (f : ZFR.Formula) (hf : ZFR.Bound f 0) (hΓ : WitnessContextCheck.Matches ws Γ) :
 TM2.Reaches machine (initial ws p Γ f) (embedded (CandidateDriver.initial p (.seq Γ f))) := by
 have h0 := scope_to_context ws p Γ f hf
 have h1 := context_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ (WitnessContextCheck.accepts ws Γ hΓ [] none (tail p Γ f) [])
 simp only [TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h1
 have h2 : TM2.Reaches machine (state (.context .accept) (some .frameEnd) (tail p Γ f) [] [] [] [])
  (embedded (CandidateDriver.initial p (.seq Γ f))) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem accepts (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert)
 (Γ : ZFR.Context) (f : ZFR.Formula) (hf : ZFR.Bound f 0) (hΓ : WitnessContextCheck.Matches ws Γ)
 (hp : ZFR.Executable.conclusion p = some (.seq Γ f)) :
 TM2.Reaches machine (initial ws p Γ f) accepted := by
 have h0 := gates_to_inference ws p Γ f hf hΓ
 have h1 := infer_run_accept ((CandidateDriver.accepts_iff p (.seq Γ f)).mpr hp)
 have h2 : TM2.Reaches machine (embedded CandidateDriver.accepted) accepted := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem infer_run_retry {c : CandidateDriver.D} (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol)
 (h : TM2.Reaches CandidateDriver.machine c (CandidateDriver.retryState v S)) :
 TM2.Reaches machine (embedded c) (embedded (CandidateDriver.retryState v S)) := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | @head a b hab hba ih =>
   by_cases hn : a.l = some .retry
   · rcases a with ⟨l,w,T⟩
     change l = some .retry at hn
     subst l
     have hstep : TM2.Reaches CandidateDriver.machine (CandidateDriver.retryState w T) b := Relation.ReflTransGen.single hab
     have hh : TM2.Reaches CandidateDriver.machine (CandidateDriver.retryState w T) (CandidateDriver.retryState v S) := hstep.trans hba
     have eq := CandidateDriver.retry_reaches w T hh
     rw [eq]
     exact Relation.ReflTransGen.refl
   · have live : b.l ≠ none := Routine.source_live CandidateDriver.machine hba (by simp [CandidateDriver.retryState])
     have ha : a.l ≠ some .accept := by
      intro he
      rcases a with ⟨l,w,T⟩
      change l = some .accept at he
      subst l
      have hd : b = ⟨none,w,T⟩ := Option.some.inj (hab.symm.trans rfl)
      exact live (hd ▸ rfl)
     rcases a with ⟨l,w,T⟩
     cases l with
     | none => simp [TM2.step] at hab
     | some q =>
       have hq : q ≠ .retry ∧ q ≠ .accept := by simpa using And.intro hn ha
       have hd : b = TM2.stepAux (CandidateDriver.machine q) w T := by simpa [TM2.step] using hab.symm
       have hs : TM2.step machine (embedded ⟨some q,w,T⟩) = some (embedded b) := by
        rw [hd]
        cases q <;> simp_all [machine,embedded,TM2.step,infer_stepAux]
       have step : TM2.Reaches machine (embedded ⟨some q,w,T⟩) (embedded b) := Relation.ReflTransGen.single hs
       exact step.trans ih

def retryState (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) : D := ⟨some .retry,v,S⟩
theorem retry_live (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) :
 TM2.step machine (retryState v S) = some (retryState v S) := rfl

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
   simp [accepted,state,retryState] at he
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
   simp [accepted,state,retryState] at he
 · exact acceptance_cannot_retry v S h


theorem rejects_gates (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert) (Γ : ZFR.Context) (f : ZFR.Formula)
 (hn : ¬(ZFR.Bound f 0 ∧ WitnessContextCheck.Matches ws Γ)) :
 ∃ v S, TM2.Reaches machine (initial ws p Γ f) (retryState v S) := by
 by_cases hf : ZFR.Bound f 0
 · have hΓ : ¬WitnessContextCheck.Matches ws Γ := by intro he; exact hn ⟨hf,he⟩
   have h0 := scope_to_context ws p Γ f hf
   obtain ⟨v,pr,a,c,h⟩ := WitnessContextCheck.rejects ws Γ hΓ [] none (tail p Γ f) []
   have h1 := context_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
   simp only [TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h1
   have h2 : TM2.Reaches machine (state (.context .reject) v pr a [] c [])
    (retryState v (ContextProgram.storage pr a [] c [])) := Relation.ReflTransGen.single rfl
   exact ⟨v,_,h0.trans (h1.trans h2)⟩
 · obtain ⟨v,pr,a,c,h⟩ := ClosedTargetGate.rejects f hf none (WitnessContextCheck.codes ws ++ .frameEnd::tail p Γ f) (TypedContext.value (.context Γ)) []
   have h0 := scope_run _ _ _ _ _ _ _ _ _ _ _ _ [] h
   have h1 : TM2.Reaches machine (state (.scope .reject) v pr a [] c [])
    (retryState v (ContextProgram.storage pr a [] c [])) := Relation.ReflTransGen.single rfl
   exact ⟨v,_,h0.trans h1⟩

theorem rejects_inference (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert) (Γ : ZFR.Context) (f : ZFR.Formula)
 (hΓ : WitnessContextCheck.Matches ws Γ) (hf : ZFR.Bound f 0) (hn : ZFR.Executable.conclusion p ≠ some (.seq Γ f)) :
 ∃ v S, TM2.Reaches machine (initial ws p Γ f) (retryState v S) := by
 have hc : ∃ v S, TM2.Reaches CandidateDriver.machine
  (CandidateDriver.initial p (.seq Γ f)) (CandidateDriver.retryState v S) := by
  have hp := ProofInterpreter.evaluates_all p
  cases he : ZFR.Executable.check p with
  | none =>
    have hr : ProofInterpreter.Rejects p := by simpa [ProofInterpreter.Evaluates,he] using hp
    exact CandidateDriver.rejected_candidate_retries p _ hr
  | some r =>
    have hr : ProofInterpreter.Runs p r.val := by simpa [ProofInterpreter.Evaluates,he] using hp
    have hne : ZFR.Row.seq Γ f ≠ r.val := by
     intro eq
     apply hn
     simp [ZFR.Executable.conclusion,he,eq]
    exact CandidateDriver.mismatched_candidate_retries p _ r.val hr hne
 obtain ⟨v,S,h⟩ := hc
 have h0 := gates_to_inference ws p Γ f hf hΓ
 have h1 := infer_run_retry v S h
 have h2 : TM2.Reaches machine (embedded (CandidateDriver.retryState v S)) (retryState v S) := Relation.ReflTransGen.single rfl
 exact ⟨v,S,h0.trans (h1.trans h2)⟩

/-- Complete canonical full-ZFR proof validation, including both infinite axiom
schemas. This is a finite candidate checker, not yet a proof-enumeration race. -/
theorem accepts_iff (ws : List ZFR.ExecutableZF.AxiomWitness) (p : ZFR.Executable.Cert) (Γ : ZFR.Context) (f : ZFR.Formula) :
 TM2.Reaches machine (initial ws p Γ f) accepted ↔
 ZFR.Bound f 0 ∧ WitnessContextCheck.Matches ws Γ ∧ ZFR.Executable.conclusion p = some (.seq Γ f) := by
 constructor
 · intro ha
   have hg : ZFR.Bound f 0 ∧ WitnessContextCheck.Matches ws Γ := by
    by_contra hn
    obtain ⟨v,S,hr⟩ := rejects_gates ws p Γ f hn
    exact retry_excludes_acceptance v S hr ha
   rcases hg with ⟨hf,hΓ⟩
   refine ⟨hf,hΓ,?_⟩
   by_contra hn
   obtain ⟨v,S,hr⟩ := rejects_inference ws p Γ f hΓ hf hn
   exact retry_excludes_acceptance v S hr ha
 · rintro ⟨hf,hΓ,hp⟩
   exact accepts ws p Γ f hf hΓ hp

end RosserDirect.ZFDriver
