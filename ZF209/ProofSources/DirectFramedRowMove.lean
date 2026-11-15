module
public import DirectTypedBlockMove
@[expose] public section
namespace RosserDirect.FramedRowMove
open Turing Segment

def machine := GrammarMove.machine FramedRowEquality.active FramedRowEquality.advance FramedRowEquality.Control.equal

theorem convert_path {q r : FramedRowEquality.Control} {xs : List Symbol}
 (h : FramedRowEquality.Path q xs r) :
 Grammar.Path FramedRowEquality.active FramedRowEquality.advance q xs r := by
 induction h with
 | nil => exact .nil _
 | cons ha h ih => exact .cons ha ih

theorem move_row (r : ZFR.Row) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.scan .tag) v (FramedRow.encode r ++ src) [] dst)
 (config .done none src [] (FramedRow.encode r ++ dst)) :=
 GrammarMove.move_word FramedRowEquality.active FramedRowEquality.advance .equal
 (by trivial) (convert_path (FramedRowEquality.row_path r)) v src dst

end RosserDirect.FramedRowMove
