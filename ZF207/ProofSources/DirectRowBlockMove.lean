module
public import DirectFramedRowMove
@[expose] public section
namespace RosserDirect.RowBlockMove
open Turing Segment
inductive Control where
 | first (q : FramedRowEquality.Control) | second (q : FramedRowEquality.Control) | done
 deriving DecidableEq, Fintype, Inhabited

def first (q : FramedRowEquality.Control) : Control := if q = .equal then .second .tag else .first q
def second (q : FramedRowEquality.Control) : Control := if q = .equal then .done else .second q
def active : Control → Prop
 | .first q | .second q => FramedRowEquality.active q
 | .done => False
instance (q : Control) : Decidable (active q) := by cases q <;> simp [active] <;> infer_instance

def advance : Control → Symbol → Control
 | .first q,x => first (FramedRowEquality.advance q x)
 | .second q,x => second (FramedRowEquality.advance q x)
 | .done,_ => .done

theorem lift_first {q r : FramedRowEquality.Control} {xs : List Symbol}
 (h : FramedRowEquality.Path q xs r) : Grammar.Path active advance (first q) xs (first r) := by
 induction h with
 | nil => exact .nil _
 | @cons q x xs r ha h ih =>
   have hn : q ≠ .equal := by intro he; subst q; exact ha
   rw [first,if_neg hn]
   exact .cons ha (by simpa only [advance] using ih)

theorem lift_second {q r : FramedRowEquality.Control} {xs : List Symbol}
 (h : FramedRowEquality.Path q xs r) : Grammar.Path active advance (second q) xs (second r) := by
 induction h with
 | nil => exact .nil _
 | @cons q x xs r ha h ih =>
   have hn : q ≠ .equal := by intro he; subst q; exact ha
   rw [second,if_neg hn]
   exact .cons ha (by simpa only [advance] using ih)

theorem pair_path (r t : ZFR.Row) :
 Grammar.Path active advance (.first .tag) (FramedRow.encode r ++ FramedRow.encode t) .done := by
 have h := (lift_first (FramedRowEquality.row_path r)).append
   (by simpa [first,second] using lift_second (FramedRowEquality.row_path t))
 simpa [first,second] using h

def machine := GrammarMove.machine active advance Control.done

theorem move_pair (r t : ZFR.Row) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.scan (.first .tag)) v (FramedRow.encode r ++ FramedRow.encode t ++ src) [] dst)
 (config .done none src [] (FramedRow.encode r ++ FramedRow.encode t ++ dst)) := by
 simpa [machine,List.append_assoc] using GrammarMove.move_word active advance Control.done (by trivial) (pair_path r t) v src dst

end RosserDirect.RowBlockMove
