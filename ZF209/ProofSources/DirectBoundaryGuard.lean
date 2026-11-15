module
public import DirectFinalRowGuard
public import DirectFramedRowMove
@[expose] public section
namespace RosserDirect.BoundaryGuard
open Turing Segment ContextProgram
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | boundary | move (q : Grammar.CopyControl FramedRowEquality.Control)
 | guard (q : FinalRowGuard.Q) | accept | reject
 deriving DecidableEq, Fintype, Inhabited
abbrev S := TM2.Stmt (fun _ : GlobalStack => Symbol) Q (Option Symbol)
def machine : Q → S
 | .boundary => .pop .program (fun _ x => x)
   (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .move (.scan .tag))) (.goto (fun _ => .reject)))
 | .move .done => .goto (fun _ => .guard .program)
 | .move .reject => .goto (fun _ => .reject)
 | .move q => Routine.relocate natRoles Q.move (FramedRowMove.machine q)
 | .guard .accept => .goto (fun _ => .accept)
 | .guard .reject => .goto (fun _ => .reject)
 | .guard q => Routine.relocate id Q.guard (FinalRowGuard.machine q)
 | .accept | .reject => .halt

def state (q : Q) (v : Option Symbol) (p a b c r : List Symbol) :
 TM2.Cfg (fun _ : GlobalStack => Symbol) Q (Option Symbol) :=
 ⟨some q,v,ContextProgram.storage p a b c r⟩
theorem agree_move q (h : FramedRowMove.machine q ≠ .halt) :
 machine (.move q) = Routine.relocate natRoles Q.move (FramedRowMove.machine q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]
theorem embed_move q v (p a b c r : List Symbol) :
 Routine.embed natRoles Q.move (config q v p b c) (ContextProgram.storage [] a [] [] r) = state (.move q) v p a b c r := by
 unfold Routine.embed config state
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem agree_guard q (h : FinalRowGuard.machine q ≠ .halt) :
 machine (.guard q) = Routine.relocate id Q.guard (FinalRowGuard.machine q) := by
 cases q <;> simp_all [machine,FinalRowGuard.machine]
theorem guard_run (q r : FinalRowGuard.Q) (v w : Option Symbol)
 (p a b c rows p' a' b' c' rows' : List Symbol)
 (h : TM2.Reaches FinalRowGuard.machine (FinalRowGuard.state q v p a b c rows) (FinalRowGuard.state r w p' a' b' c' rows')) :
 TM2.Reaches machine (state (.guard q) v p a b c rows) (state (.guard r) w p' a' b' c' rows') := by
 obtain ⟨d,hd,hr,he⟩ := Routine.lift_run id Function.injective_id Q.guard FinalRowGuard.machine machine agree_guard h
  (by simp [FinalRowGuard.state])
  (show Routine.Related id Q.guard (FinalRowGuard.state q v p a b c rows) (state (.guard q) v p a b c rows) from ⟨rfl,rfl,rfl⟩)
 have eq : d = state (.guard r) w p' a' b' c' rows' := by
  rcases d with ⟨l,z,S⟩
  rcases hr with ⟨hl,hv,hs⟩
  change l = some (.guard r) at hl
  change z = w at hv
  change S = ContextProgram.storage p' a' b' c' rows' at hs
  subst l; subst z; subst S
  rfl
 exact eq ▸ hd

/-- A frame-end boundary and exact expected row can live after the certificate
program while the checker uses its ordinary work stacks. This adapter consumes
that boundary/row and invokes the exact-single-result guard. -/
theorem accepts (r : ZFR.Row) (v : Option Symbol) :
 TM2.Reaches machine
 (state .boundary v (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode r))
 (state .accept none [] [] [] [] []) := by
 have h0 : TM2.Reaches machine
  (state .boundary v (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode r))
  (state (.move (.scan .tag)) (some .frameEnd) (FramedRow.encode r) [] [] [] (FramedRow.encode r)) := Relation.ReflTransGen.single (by
   simp [machine,state,TM2.step,TM2.stepAux,ContextProgram.storage]
   funext j; cases j <;> rfl)
 have h1 := Routine.lift_embedded_run natRoles nat_injective Q.move FramedRowMove.machine machine agree_move
  (ContextProgram.storage [] [] [] [] (FramedRow.encode r)) (FramedRowMove.move_row r (some .frameEnd) [] []) (by simp [config])
 simp only [embed_move,List.append_nil] at h1
 have h2 : TM2.Reaches machine
  (state (.move .done) none [] [] [] (FramedRow.encode r) (FramedRow.encode r))
  (state (.guard .program) none [] [] [] (FramedRow.encode r) (FramedRow.encode r)) := Relation.ReflTransGen.single rfl
 have h3 := guard_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FinalRowGuard.accepts r none)
 have h4 : TM2.Reaches machine (state (.guard .accept) none [] [] [] [] []) (state .accept none [] [] [] [] []) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem rejects_wrong_row (r s : ZFR.Row) (hne : r ≠ s) (v : Option Symbol) :
 ∃ w left right, TM2.Reaches machine
 (state .boundary v (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode s))
 (state .reject w [] [] [] left right) := by
 have h0 : TM2.Reaches machine
  (state .boundary v (.frameEnd :: FramedRow.encode r) [] [] [] (FramedRow.encode s))
  (state (.move (.scan .tag)) (some .frameEnd) (FramedRow.encode r) [] [] [] (FramedRow.encode s)) := Relation.ReflTransGen.single (by
   simp [machine,state,TM2.step,TM2.stepAux,ContextProgram.storage]
   funext j; cases j <;> rfl)
 have h1 := Routine.lift_embedded_run natRoles nat_injective Q.move FramedRowMove.machine machine agree_move
  (ContextProgram.storage [] [] [] [] (FramedRow.encode s)) (FramedRowMove.move_row r (some .frameEnd) [] []) (by simp [config])
 simp only [embed_move,List.append_nil] at h1
 have h2 : TM2.Reaches machine
  (state (.move .done) none [] [] [] (FramedRow.encode r) (FramedRow.encode s))
  (state (.guard .program) none [] [] [] (FramedRow.encode r) (FramedRow.encode s)) := Relation.ReflTransGen.single rfl
 obtain ⟨w,left,right,h⟩ := FinalRowGuard.rejects_wrong_row r s hne none
 have h3 := guard_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
 have h4 : TM2.Reaches machine (state (.guard .reject) w [] [] [] left right)
  (state .reject w [] [] [] left right) := Relation.ReflTransGen.single rfl
 exact ⟨w,left,right,h0.trans (h1.trans (h2.trans (h3.trans h4)))⟩
end RosserDirect.BoundaryGuard
