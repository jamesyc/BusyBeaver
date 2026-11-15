module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.FinalRowGuard
open Turing Segment ContextProgram
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | program | values | scratch | compare (q : FramedRowEquality.Control)
 | expectedTail | actualTail | accept | reject
 deriving DecidableEq, Fintype, Inhabited
abbrev S := TM2.Stmt (fun _ : GlobalStack => Symbol) Q (Option Symbol)
def empty (k : GlobalStack) (next : Q) : S :=
 .peek k (fun _ x => x) (.branch Option.isNone (.goto (fun _ => next)) (.goto (fun _ => .reject)))
def machine : Q → S
 | .program => empty .program .values
 | .values => empty .values .scratch
 | .scratch => empty .scratch (.compare .tag)
 | .compare .equal => .goto (fun _ => .expectedTail)
 | .compare .different => .goto (fun _ => .reject)
 | .compare q => Routine.relocate premiseRoles Q.compare (FramedRowEquality.machine q)
 | .expectedTail => empty .temporary .actualTail
 | .actualTail => empty .rows .accept
 | .accept | .reject => .halt

def state (q : Q) (v : Option Symbol) (p a b c r : List Symbol) :
 TM2.Cfg (fun _ : GlobalStack => Symbol) Q (Option Symbol) :=
 ⟨some q,v,ContextProgram.storage p a b c r⟩
theorem agree_compare q (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.compare q) = Routine.relocate premiseRoles Q.compare (FramedRowEquality.machine q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]
theorem embed_compare q v (p a b c r : List Symbol) :
 Routine.embed premiseRoles Q.compare (config q v c b r) (ContextProgram.storage p a [] [] []) =
 state (.compare q) v p a b c r := by
 unfold Routine.embed config state
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl

theorem prepare (v : Option Symbol) (expected actual : List Symbol) :
 TM2.Reaches machine (state .program v [] [] [] expected actual)
 (state (.compare .tag) none [] [] [] expected actual) := by
 have h0 : TM2.Reaches machine (state .program v [] [] [] expected actual)
  (state .values none [] [] [] expected actual) := Relation.ReflTransGen.single rfl
 have h1 : TM2.Reaches machine (state .values none [] [] [] expected actual)
  (state .scratch none [] [] [] expected actual) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine (state .scratch none [] [] [] expected actual)
  (state (.compare .tag) none [] [] [] expected actual) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem finish (v : Option Symbol) :
 TM2.Reaches machine (state (.compare .equal) v [] [] [] [] [])
 (state .accept none [] [] [] [] []) := by
 have h0 : TM2.Reaches machine (state (.compare .equal) v [] [] [] [] [])
  (state .expectedTail v [] [] [] [] []) := Relation.ReflTransGen.single rfl
 have h1 : TM2.Reaches machine (state .expectedTail v [] [] [] [] [])
  (state .actualTail none [] [] [] [] []) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine (state .actualTail none [] [] [] [] [])
  (state .accept none [] [] [] [] []) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

/-- Guard accepts exactly matched canonical single-row inputs with empty program,
operand and scratch stacks. This alone does not validate ZF assumptions. -/
theorem accepts (r : ZFR.Row) (v : Option Symbol) :
 TM2.Reaches machine (state .program v [] [] [] (FramedRow.encode r) (FramedRow.encode r))
 (state .accept none [] [] [] [] []) := by
 obtain ⟨w,h⟩ := FramedRowEquality.equal_rows_exact r none [] [] []
 have hc := Routine.lift_embedded_run premiseRoles premise_injective Q.compare
  FramedRowEquality.machine machine agree_compare (ContextProgram.storage [] [] [] [] []) h (by simp [config])
 simp only [embed_compare,List.append_nil] at hc
 exact (prepare v _ _).trans (hc.trans (finish w))

theorem rejects_wrong_row (r s : ZFR.Row) (hne : r ≠ s) (v : Option Symbol) :
 ∃ w left right, TM2.Reaches machine (state .program v [] [] [] (FramedRow.encode r) (FramedRow.encode s))
 (state .reject w [] [] [] left right) := by
 obtain ⟨w,left,right,h⟩ := FramedRowEquality.compare_rows r s none [] [] []
 simp only [hne,↓reduceIte,List.append_nil] at h
 have hc := Routine.lift_embedded_run premiseRoles premise_injective Q.compare
  FramedRowEquality.machine machine agree_compare (ContextProgram.storage [] [] [] [] []) h (by simp [config])
 simp only [embed_compare] at hc
 have he : TM2.Reaches machine (state (.compare .different) w [] [] [] left right)
  (state .reject w [] [] [] left right) := Relation.ReflTransGen.single rfl
 exact ⟨w,left,right,(prepare v _ _).trans (hc.trans he)⟩

end RosserDirect.FinalRowGuard
