module
public import DirectSelectSecond
public import DirectRowBlockMove
@[expose] public section
namespace RosserDirect.RowSwap
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | first (q : Grammar.CopyControl FramedRowEquality.Control)
 | second (q : Grammar.CopyControl FramedRowEquality.Control)
 | back (q : Grammar.CopyControl RowBlockMove.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .first .done => .goto (fun _ => .second (.scan .tag))
 | .first q => Routine.relocate id Control.first (FramedRowMove.machine q)
 | .second .done => .goto (fun _ => .back (.scan (.first .tag)))
 | .second q => Routine.relocate id Control.second (FramedRowMove.machine q)
 | .back .done => .goto (fun _ => .done)
 | .back q => Routine.relocate SelectSecond.swap Control.back (RowBlockMove.machine q)
 | .done => .halt

theorem agree_first (q : Grammar.CopyControl FramedRowEquality.Control) (h : FramedRowMove.machine q ≠ .halt) :
 machine (.first q) = Routine.relocate id Control.first (FramedRowMove.machine q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]
theorem agree_second (q : Grammar.CopyControl FramedRowEquality.Control) (h : FramedRowMove.machine q ≠ .halt) :
 machine (.second q) = Routine.relocate id Control.second (FramedRowMove.machine q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]
theorem agree_back (q : Grammar.CopyControl RowBlockMove.Control) (h : RowBlockMove.machine q ≠ .halt) :
 machine (.back q) = Routine.relocate SelectSecond.swap Control.back (RowBlockMove.machine q) := by
 cases q <;> simp_all [machine,RowBlockMove.machine,GrammarMove.machine]

theorem embed_first (q : Grammar.CopyControl FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.first (config q v a b c) (fun _ => []) = config (.first q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_second (q : Grammar.CopyControl FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.second (config q v a b c) (fun _ => []) = config (.second q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_back (q : Grammar.CopyControl RowBlockMove.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.back (config q v a b c) (fun _ => []) = config (.back q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Swap two arbitrary framed proof rows, preserving both surrounding tails. -/
theorem swap_rows (a b : ZFR.Row) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.first (.scan .tag)) v (FramedRow.encode b ++ FramedRow.encode a ++ src) [] dst)
 (config .done none (FramedRow.encode a ++ FramedRow.encode b ++ src) [] dst) := by
 have hf := Routine.lift_embedded_run id Function.injective_id Control.first
   FramedRowMove.machine machine agree_first (fun _ => [])
   (FramedRowMove.move_row b v (FramedRow.encode a ++ src) dst) (by simp [config])
 simp only [embed_first] at hf
 have hfl : TM2.Reaches machine
   (config (.first .done) none (FramedRow.encode a ++ src) [] (FramedRow.encode b ++ dst))
   (config (.second (.scan .tag)) none (FramedRow.encode a ++ src) [] (FramedRow.encode b ++ dst)) := Relation.ReflTransGen.single rfl
 have hs := Routine.lift_embedded_run id Function.injective_id Control.second
   FramedRowMove.machine machine agree_second (fun _ => [])
   (FramedRowMove.move_row a none src (FramedRow.encode b ++ dst)) (by simp [config])
 simp only [embed_second] at hs
 have hsl : TM2.Reaches machine
   (config (.second .done) none src [] (FramedRow.encode a ++ FramedRow.encode b ++ dst))
   (config (.back (.scan (.first .tag))) none src [] (FramedRow.encode a ++ FramedRow.encode b ++ dst)) := Relation.ReflTransGen.single rfl
 have hb := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.back
   RowBlockMove.machine machine agree_back (fun _ => [])
   (RowBlockMove.move_pair a b none dst src) (by simp [config])
 simp only [embed_back] at hb
 have hbl : TM2.Reaches machine
   (config (.back .done) none (FramedRow.encode a ++ FramedRow.encode b ++ src) [] dst)
   (config .done none (FramedRow.encode a ++ FramedRow.encode b ++ src) [] dst) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at hf hfl hs hsl hb hbl ⊢
 exact hf.trans (hfl.trans (hs.trans (hsl.trans (hb.trans hbl))))

end RosserDirect.RowSwap
