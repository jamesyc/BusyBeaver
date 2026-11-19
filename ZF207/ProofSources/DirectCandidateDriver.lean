module
public import DirectBoundaryGuard
@[expose] public section
namespace RosserDirect.CandidateDriver
open Turing
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | run (q : ContextProgram.Control) | check (q : BoundaryGuard.Q) | retry | accept
 deriving DecidableEq, Fintype, Inhabited
abbrev C := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) ContextProgram.Control (Option Symbol)
abbrev D := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
abbrev S := TM2.Stmt (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
def route : ContextProgram.GlobalStmt → S
 | .push k f s => .push k f (route s)
 | .peek k f s => .peek k f (route s)
 | .pop k f s => .pop k f (route s)
 | .load f s => .load f (route s)
 | .branch f s t => .branch f (route s) (route t)
 | .goto f => .goto (fun v => .run (f v))
 | .halt => .goto (fun _ => .retry)
def routed (c : C) : D :=
 ⟨some (match c.l with | none => .retry | some q => .run q),c.var,c.stk⟩
def embedded (c : C) : D := ⟨c.l.map Q.run,c.var,c.stk⟩
theorem route_correct (s : ContextProgram.GlobalStmt) v S :
 TM2.stepAux (route s) v S = routed (TM2.stepAux s v S) := by
 induction s generalizing v S with
 | push k f s ih => exact ih _ _
 | peek k f s ih => exact ih _ _
 | pop k f s ih => exact ih _ _
 | load f s ih => exact ih _ _
 | branch f s t ihs iht =>
   simp only [route,TM2.stepAux]
   cases f v
   · exact iht _ _
   · exact ihs _ _
 | goto f => rfl
 | halt => rfl

def machine : Q → S
 | .run q => if q = .dispatch .start then
   .peek .program (fun _ x => x)
    (.branch (fun x => x == some .frameEnd)
     (.goto (fun _ => .check .boundary)) (route (ContextProgram.machine q)))
   else route (ContextProgram.machine q)
 | .check .accept => .goto (fun _ => .accept)
 | .check .reject => .goto (fun _ => .retry)
 | .check q => Routine.relocate id Q.check (BoundaryGuard.machine q)
 | .retry => .goto (fun _ => .retry)
 | .accept => .halt

/-- No reset/enumerator is installed yet: retry is deliberately a live self-loop,
not an accepting halt. The final race must replace it with next-candidate work. -/
theorem retry_live (v : Option Symbol) (S : ContextProgram.GlobalStack → List Symbol) :
 TM2.step machine ⟨some .retry,v,S⟩ = some ⟨some .retry,v,S⟩ := rfl

def AtBoundary (c : C) : Prop :=
 c.l = some (.dispatch .start) ∧ (c.stk .program).head? = some .frameEnd

theorem ordinary_aux (q : ContextProgram.Control) (v : Option Symbol)
 (S : ContextProgram.GlobalStack → List Symbol)
 (hn : ¬AtBoundary ⟨some q,v,S⟩) :
 TM2.stepAux (machine (.run q)) v S = TM2.stepAux (route (ContextProgram.machine q)) v S := by
 by_cases hq : q = .dispatch .start
 · subst q
   have hh : (S .program).head? ≠ some .frameEnd := by simpa [AtBoundary] using hn
   cases hs : S .program with
   | nil =>
     simp [machine,ContextProgram.machine,Routine.relocate,OpcodeDispatch.machine,OpcodeDispatch.active,
      TM2.stepAux,route,ContextProgram.dispatchRoles,hs]
   | cons x xs =>
     cases x <;> simp_all [machine,ContextProgram.machine,Routine.relocate,OpcodeDispatch.machine,
      OpcodeDispatch.active,TM2.stepAux,route,ContextProgram.dispatchRoles,OpcodeDispatch.advance]
 · simp [machine,hq]

theorem live_step {c d : C} (h : TM2.step ContextProgram.machine c = some d)
 (live : d.l ≠ none) (hn : ¬AtBoundary c) :
 TM2.step machine (embedded c) = some (embedded d) := by
 rcases c with ⟨l,v,S⟩
 cases l with
 | none => simp [TM2.step] at h
 | some q =>
   have hd : d = TM2.stepAux (ContextProgram.machine q) v S := by simpa [TM2.step] using h.symm
   subst d
   simp only [embedded,Option.map_some,TM2.step]
   rw [ordinary_aux q v S hn,route_correct]
   congr 1
   rcases he : TM2.stepAux (ContextProgram.machine q) v S with ⟨l,w,T⟩
   cases l with
   | none => exact False.elim (live (by rw [he]))
   | some r => rfl

/-- Boundary interception occurs before the delimiter is consumed. -/
theorem boundary_step (v : Option Symbol) (p a b c rows : List Symbol) :
 TM2.step machine (embedded (ContextProgram.cfg (.dispatch .start) v (.frameEnd::p) a b c rows)) =
 some ⟨some (.check .boundary),some .frameEnd,ContextProgram.storage (.frameEnd::p) a b c rows⟩ := by
 simp [machine,embedded,ContextProgram.cfg,TM2.step,TM2.stepAux,ContextProgram.storage]

theorem rejected_cannot_return {c d : C}
 (hc : c.l = some (.dispatch .reject)) (hd : d.l = some (.dispatch .start)) :
 ¬TM2.Reaches ContextProgram.machine c d := by
 intro h
 rcases c with ⟨l,v,S⟩
 change l = some (.dispatch .reject) at hc
 subst l
 rcases Relation.ReflTransGen.cases_head h with eq | ⟨b,hb,hbd⟩
 · have he := congrArg TM2.Cfg.l eq
   simp [hd] at he
 · have step : TM2.step ContextProgram.machine ⟨some (.dispatch .reject),v,S⟩ = some ⟨none,v,S⟩ := rfl
   have eq : b = ⟨none,v,S⟩ := Option.some.inj (hb.symm.trans step)
   subst b
   have eq := Routine.dead_reaches ContextProgram.machine rfl hbd
   have he := congrArg TM2.Cfg.l eq
   simp [hd] at he

theorem boundary_successor_rejects {c d : C} (hc : AtBoundary c)
 (hs : TM2.step ContextProgram.machine c = some d) : d.l = some (.dispatch .reject) := by
 rcases c with ⟨l,v,S⟩
 rcases hc with ⟨hl,hh⟩
 change l = some (.dispatch .start) at hl
 subst l
 change (S .program).head? = some .frameEnd at hh
 cases hp : S .program with
 | nil => simp [hp] at hh
 | cons x xs =>
   have hx : x = .frameEnd := by simpa [hp] using hh
   subst x
   have he : d = TM2.stepAux (ContextProgram.machine (.dispatch .start)) v S := by simpa [TM2.step] using hs.symm
   rw [he]
   simp [ContextProgram.machine,Routine.relocate,OpcodeDispatch.machine,OpcodeDispatch.active,
    TM2.stepAux,ContextProgram.dispatchRoles,hp,OpcodeDispatch.advance]

/-- Every source trace returning to dispatch is preserved up to that return.
A delimiter cannot be intercepted early on such a trace: in the source machine
it immediately enters terminal rejection and cannot return to dispatch. -/
theorem live_run_to_return {c d : C} (h : TM2.Reaches ContextProgram.machine c d)
 (hd : d.l = some (.dispatch .start)) :
 TM2.Reaches machine (embedded c) (embedded d) := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | @head a b hab hbd ih =>
   have live : b.l ≠ none := Routine.source_live ContextProgram.machine hbd (by simp [hd])
   have hn : ¬AtBoundary a := by
    intro ha
    exact rejected_cannot_return (boundary_successor_rejects ha hab) hd hbd
   have step : TM2.Reaches machine (embedded a) (embedded b) := Relation.ReflTransGen.single (live_step hab live hn)
   exact step.trans ih

theorem rejected_labels {c d : C}
 (hc : c.l = some (.dispatch .reject)) (h : TM2.Reaches ContextProgram.machine c d) :
 d.l = some (.dispatch .reject) ∨ d.l = none := by
 rcases c with ⟨l,v,S⟩
 change l = some (.dispatch .reject) at hc
 subst l
 rcases Relation.ReflTransGen.cases_head h with eq | ⟨b,hb,hbd⟩
 · exact Or.inl (congrArg TM2.Cfg.l eq).symm
 · have step : TM2.step ContextProgram.machine ⟨some (.dispatch .reject),v,S⟩ = some ⟨none,v,S⟩ := rfl
   have eq : b = ⟨none,v,S⟩ := Option.some.inj (hb.symm.trans step)
   subst b
   exact Or.inr (congrArg TM2.Cfg.l (Routine.dead_reaches ContextProgram.machine rfl hbd))

theorem live_run_to_reject {c d : C} (h : TM2.Reaches ContextProgram.machine c d)
 (hd : d.l = some .proofReject) : TM2.Reaches machine (embedded c) (embedded d) := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | @head a b hab hbd ih =>
   have live : b.l ≠ none := Routine.source_live ContextProgram.machine hbd (by simp [hd])
   have hn : ¬AtBoundary a := by
    intro ha
    rcases rejected_labels (boundary_successor_rejects ha hab) hbd with he | he
    all_goals simp [hd] at he
   have step : TM2.Reaches machine (embedded a) (embedded b) := Relation.ReflTransGen.single (live_step hab live hn)
   exact step.trans ih

theorem rejection_to_retry (v : Option Symbol) (p a b c r : List Symbol) :
 TM2.step machine (embedded (ContextProgram.cfg .proofReject v p a b c r)) =
 some ⟨some .retry,v,ContextProgram.storage p a b c r⟩ := rfl
end RosserDirect.CandidateDriver
