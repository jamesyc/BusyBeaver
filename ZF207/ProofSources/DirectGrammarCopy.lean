module
public import DirectFramedRowCopy
@[expose] public section
namespace RosserDirect.Grammar
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Path {Q : Type} (active : Q → Prop) (advance : Q → Symbol → Q) : Q → List Symbol → Q → Prop where
 | nil (q) : Path active advance q [] q
 | cons {q x xs r} : active q → Path active advance (advance q x) xs r → Path active advance q (x :: xs) r

theorem Path.append {Q : Type} {active : Q → Prop} {advance : Q → Symbol → Q}
    {q r s : Q} {xs ys : List Symbol}
    (h : Path active advance q xs r) (g : Path active advance r ys s) : Path active advance q (xs ++ ys) s := by
 induction h with
 | nil => exact g
 | cons ha h ih => exact .cons ha (ih g)

inductive CopyControl (Q : Type) where
 | scan (q : Q) | flush | done | reject
 deriving DecidableEq, Fintype, Inhabited

variable {Q : Type} [DecidableEq Q] (active : Q → Prop) [∀ q, Decidable (active q)]
    (advance : Q → Symbol → Q) (accept : Q)

def copyMachine : CopyControl Q → Stmt (CopyControl Q)
 | .scan q =>
   if q = accept then .goto (fun _ => .flush) else
   if active q then .pop .input (fun _ x => x)
    (.branch Option.isSome
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun x => .scan (advance q (x.getD .bit0)))))
     (.goto (fun _ => .reject)))
   else .goto (fun _ => .reject)
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .input (fun x => x.getD .bit0)
     (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .flush)))))
 | .done | .reject => .halt

theorem scan_step (notActive : ¬active accept) (q : Q) (ha : active q)
    (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (copyMachine active advance accept) (config (.scan q) v (x :: a) s c) =
 some (config (.scan (advance q x)) (some x) a (x :: s) c) := by
 have hn : q ≠ accept := by intro he; exact notActive (he ▸ ha)
 cases x <;> simp [copyMachine,hn,ha,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_accept (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (copyMachine active advance accept) (config (.scan accept) v a s c) =
 some (config .flush v a s c) := by simp [copyMachine,config,TM2.step,TM2.stepAux]

theorem scan_path (notActive : ¬active accept) {q : Q} {p : List Symbol}
    (hp : Path active advance q p accept) (v : Option Symbol) (a s c : List Symbol) :
 ∃ w, TM2.Reaches (copyMachine active advance accept) (config (.scan q) v (p ++ a) s c)
   (config .flush w a (p.reverse ++ s) c) := by
 induction p generalizing q v s with
 | nil =>
   cases hp
   exact ⟨v,Relation.ReflTransGen.single (scan_accept active advance accept v a s c)⟩
 | cons x xs ih =>
   cases hp with
   | cons ha hp =>
     obtain ⟨w,hw⟩ := ih hp (some x) (x :: s)
     have one : TM2.Reaches (copyMachine active advance accept)
       (config (.scan q) v ((x :: xs) ++ a) s c)
       (config (.scan (advance q x)) (some x) (xs ++ a) (x :: s) c) :=
       Relation.ReflTransGen.single (by rw [List.cons_append,scan_step active advance accept notActive q ha]; rfl)
     exact ⟨w,by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using one.trans hw⟩

theorem flush_step (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (copyMachine active advance accept) (config .flush v a (x :: s) c) =
 some (config .flush (some x) (x :: a) s (x :: c)) := by
 cases x <;> simp [copyMachine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem flush_empty (v : Option Symbol) (a c : List Symbol) :
 TM2.step (copyMachine active advance accept) (config .flush v a [] c) =
 some (config .done none a [] c) := by simp [copyMachine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem flush_all (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches (copyMachine active advance accept) (config .flush v a s c)
   (config .done none (s.reverse ++ a) [] (s.reverse ++ c)) := by
 induction s generalizing v a c with
 | nil => exact Relation.ReflTransGen.single (flush_empty active advance accept v a c)
 | cons x xs ih =>
   have one : TM2.Reaches (copyMachine active advance accept) (config .flush v a (x :: xs) c)
     (config .flush (some x) (x :: a) xs (x :: c)) :=
     Relation.ReflTransGen.single (flush_step active advance accept x v a xs c)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some x) (x :: a) (x :: c))

/-- One generic verified copier serves any finite prefix grammar. -/
theorem copy_word (notActive : ¬active accept) {q : Q} {p : List Symbol}
    (hp : Path active advance q p accept) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (copyMachine active advance accept) (config (.scan q) v (p ++ src) [] dst)
   (config .done none (p ++ src) [] (p ++ dst)) := by
 obtain ⟨w,hs⟩ := scan_path active advance accept notActive hp v src [] dst
 have h := hs.trans (flush_all active advance accept w src (p.reverse ++ []) dst)
 simpa [TM2.Reaches] using h

end RosserDirect.Grammar
