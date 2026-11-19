module
public import DirectFramedRowEquality
@[expose] public section
namespace RosserDirect.FramedRowCopy
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | scan (phase : FramedRowEquality.Control) | flush | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .scan .equal => .goto (fun _ => .flush)
 | .scan .different => .goto (fun _ => .reject)
 | .scan q => .pop .input (fun _ x => x)
   (.branch Option.isSome
    (.push .scratch (fun x => x.getD .bit0)
     (.goto (fun x => .scan (FramedRowEquality.advance q (x.getD .bit0)))))
    (.goto (fun _ => .reject)))
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .input (fun x => x.getD .bit0)
     (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .flush)))))
 | .done | .reject => .halt

theorem scan_step (q : FramedRowEquality.Control) (ha : FramedRowEquality.active q)
    (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config (.scan q) v (x :: a) s c) =
 some (config (.scan (FramedRowEquality.advance q x)) (some x) a (x :: s) c) := by
 cases q <;> cases x <;> simp_all [FramedRowEquality.active,machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_equal (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config (.scan .equal) v a s c) = some (config .flush v a s c) := rfl

theorem scan_path {q : FramedRowEquality.Control} {p : List Symbol}
    (hp : FramedRowEquality.Path q p .equal)
    (v : Option Symbol) (a s c : List Symbol) :
 ∃ w, TM2.Reaches machine (config (.scan q) v (p ++ a) s c)
   (config .flush w a (p.reverse ++ s) c) := by
 induction p generalizing q v s with
 | nil =>
   cases hp
   exact ⟨v,Relation.ReflTransGen.single (scan_equal v a s c)⟩
 | cons x xs ih =>
   cases hp with
   | cons ha hp =>
     obtain ⟨w,hw⟩ := ih hp (some x) (x :: s)
     have one : TM2.Reaches machine
       (config (.scan q) v ((x :: xs) ++ a) s c)
       (config (.scan (FramedRowEquality.advance q x)) (some x) (xs ++ a) (x :: s) c) :=
       Relation.ReflTransGen.single (by rw [List.cons_append,scan_step q ha]; rfl)
     exact ⟨w,by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using one.trans hw⟩

theorem flush_step (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config .flush v a (x :: s) c) =
 some (config .flush (some x) (x :: a) s (x :: c)) := by
 cases x <;> simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem flush_empty (v : Option Symbol) (a c : List Symbol) :
 TM2.step machine (config .flush v a [] c) = some (config .done none a [] c) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem flush_all (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (config .flush v a s c)
   (config .done none (s.reverse ++ a) [] (s.reverse ++ c)) := by
 induction s generalizing v a c with
 | nil => exact Relation.ReflTransGen.single (flush_empty v a c)
 | cons x xs ih =>
   have one : TM2.Reaches machine (config .flush v a (x :: xs) c)
     (config .flush (some x) (x :: a) xs (x :: c)) := Relation.ReflTransGen.single (flush_step x v a xs c)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some x) (x :: a) (x :: c))

/-- Copies exactly one complete row, restoring the input and preserving both
trailing stacks. Internal context delimiters never end the copy prematurely. -/
theorem copy_row (r : ZFR.Row) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
   (config (.scan .tag) v (FramedRow.encode r ++ src) [] dst)
   (config .done none (FramedRow.encode r ++ src) [] (FramedRow.encode r ++ dst)) := by
 obtain ⟨w,hs⟩ := scan_path (FramedRowEquality.row_path r) v src [] dst
 have h := hs.trans (flush_all w src ((FramedRow.encode r).reverse ++ []) dst)
 simpa [TM2.Reaches] using h

end RosserDirect.FramedRowCopy
