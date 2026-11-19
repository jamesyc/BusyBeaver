module
public import DirectTypedBlockCopy
@[expose] public section
namespace RosserDirect.GrammarMove
open Turing Segment Grammar
set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [DecidableEq Q] (active : Q → Prop) [∀ q, Decidable (active q)]
    (advance : Q → Symbol → Q) (accept : Q)

def machine : CopyControl Q → Stmt (CopyControl Q)
 | .scan q =>
   if q = accept then .goto (fun _ => .flush) else
   if active q then .pop .input (fun _ x => x)
    (.branch Option.isSome
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun x => .scan (advance q (x.getD .bit0)))))
     (.goto (fun _ => .reject)))
   else .goto (fun _ => .reject)
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .flush))))
 | .done | .reject => .halt

theorem scan_step (notActive : ¬active accept) (q : Q) (ha : active q)
    (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (machine active advance accept) (config (.scan q) v (x :: a) s c) =
 some (config (.scan (advance q x)) (some x) a (x :: s) c) := by
 have hn : q ≠ accept := by intro he; exact notActive (he ▸ ha)
 cases x <;> simp [machine,hn,ha,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_accept (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (machine active advance accept) (config (.scan accept) v a s c) =
 some (config .flush v a s c) := by simp [machine,config,TM2.step,TM2.stepAux]

theorem scan_path (notActive : ¬active accept) {q : Q} {p : List Symbol}
    (hp : Path active advance q p accept) (v : Option Symbol) (a s c : List Symbol) :
 ∃ w, TM2.Reaches (machine active advance accept) (config (.scan q) v (p ++ a) s c)
   (config .flush w a (p.reverse ++ s) c) := by
 induction p generalizing q v s with
 | nil =>
   cases hp
   exact ⟨v,Relation.ReflTransGen.single (scan_accept active advance accept v a s c)⟩
 | cons x xs ih =>
   cases hp with
   | cons ha hp =>
     obtain ⟨w,hw⟩ := ih hp (some x) (x :: s)
     have one : TM2.Reaches (machine active advance accept)
       (config (.scan q) v ((x :: xs) ++ a) s c)
       (config (.scan (advance q x)) (some x) (xs ++ a) (x :: s) c) :=
       Relation.ReflTransGen.single (by rw [List.cons_append,scan_step active advance accept notActive q ha]; rfl)
     exact ⟨w,by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using one.trans hw⟩

theorem flush_step (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (machine active advance accept) (config .flush v a (x :: s) c) =
 some (config .flush (some x) a s (x :: c)) := by
 cases x <;> simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem flush_empty (v : Option Symbol) (a c : List Symbol) :
 TM2.step (machine active advance accept) (config .flush v a [] c) =
 some (config .done none a [] c) := by simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem flush_all (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches (machine active advance accept) (config .flush v a s c)
   (config .done none a [] (s.reverse ++ c)) := by
 induction s generalizing v a c with
 | nil => exact Relation.ReflTransGen.single (flush_empty active advance accept v a c)
 | cons x xs ih =>
   have one : TM2.Reaches (machine active advance accept) (config .flush v a (x :: xs) c)
     (config .flush (some x) a xs (x :: c)) :=
     Relation.ReflTransGen.single (flush_step active advance accept x v a xs c)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some x) a (x :: c))

/-- One generic verified mover serves any finite prefix grammar. -/
theorem move_word (notActive : ¬active accept) {q : Q} {p : List Symbol}
    (hp : Path active advance q p accept) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine active advance accept) (config (.scan q) v (p ++ src) [] dst)
   (config .done none src [] (p ++ dst)) := by
 obtain ⟨w,hs⟩ := scan_path active advance accept notActive hp v src [] dst
 have h := hs.trans (flush_all active advance accept w src (p.reverse ++ []) dst)
 simpa [TM2.Reaches] using h

end RosserDirect.GrammarMove

namespace RosserDirect.TypedBlock
open Turing Segment

def moveMachine := GrammarMove.machine active advance Control.done

theorem move_block (n : Fin 6) (vs : List ZFR.TokenVM.Value) (len : vs.length = n.val+1)
 (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches moveMachine
 (config (.scan (.run n .start)) v (TypedContext.stack vs ++ src) [] dst)
 (config .done none src [] (TypedContext.stack vs ++ dst)) :=
 GrammarMove.move_word active advance Control.done (by trivial) (block_path n vs len) v src dst

end RosserDirect.TypedBlock
