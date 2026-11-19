module
public import DirectTypedBlockCopy
@[expose] public section
namespace RosserDirect.Grammar
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive DropControl (Q : Type) where
 | scan (q : Q) | done | reject
 deriving DecidableEq, Fintype, Inhabited

variable {Q : Type} [DecidableEq Q] (active : Q → Prop) [∀ q, Decidable (active q)]
 (advance : Q → Symbol → Q) (accept : Q)

def dropMachine : DropControl Q → Stmt (DropControl Q)
 | .scan q =>
   if q = accept then .goto (fun _ => .done) else
   if active q then .pop .input (fun _ x => x)
    (.branch Option.isSome (.goto (fun x => .scan (advance q (x.getD .bit0))))
      (.goto (fun _ => .reject)))
   else .goto (fun _ => .reject)
 | .done | .reject => .halt

theorem drop_step (notActive : ¬active accept) (q : Q) (ha : active q)
 (x : Symbol) (v : Option Symbol) (src scr dst : List Symbol) :
 TM2.step (dropMachine active advance accept) (config (.scan q) v (x :: src) scr dst) =
 some (config (.scan (advance q x)) (some x) src scr dst) := by
 have hn : q ≠ accept := by intro he; exact notActive (he ▸ ha)
 cases x <;> simp [dropMachine,hn,ha,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem drop_accept (v : Option Symbol) (src scr dst : List Symbol) :
 TM2.step (dropMachine active advance accept) (config (.scan accept) v src scr dst) =
 some (config .done v src scr dst) := by simp [dropMachine,config,TM2.step,TM2.stepAux]

/-- Discard one grammar-delimited word, preserving all suffix and work stacks. -/
theorem drop_word (notActive : ¬active accept) {q : Q} {p : List Symbol}
 (hp : Path active advance q p accept) (v : Option Symbol) (src scr dst : List Symbol) :
 ∃ w, TM2.Reaches (dropMachine active advance accept)
 (config (.scan q) v (p ++ src) scr dst) (config .done w src scr dst) := by
 induction p generalizing q v with
 | nil =>
   cases hp
   exact ⟨v,Relation.ReflTransGen.single (drop_accept active advance accept v src scr dst)⟩
 | cons x xs ih =>
   cases hp with
   | cons ha hp =>
     obtain ⟨w,hw⟩ := ih hp (some x)
     have one : TM2.Reaches (dropMachine active advance accept)
       (config (.scan q) v (x :: (xs ++ src)) scr dst)
       (config (.scan (advance q x)) (some x) (xs ++ src) scr dst) :=
       Relation.ReflTransGen.single (drop_step active advance accept notActive q ha x v (xs ++ src) scr dst)
     exact ⟨w,one.trans hw⟩

end RosserDirect.Grammar

namespace RosserDirect.TypedBlock
open Turing Segment

def dropMachine := Grammar.dropMachine active advance Control.done

theorem drop_block (n : Fin 6) (vs : List ZFR.TokenVM.Value) (len : vs.length = n.val+1)
 (v : Option Symbol) (src scr dst : List Symbol) :
 ∃ w, TM2.Reaches dropMachine
 (config (.scan (.run n .start)) v (TypedContext.stack vs ++ src) scr dst)
 (config .done w src scr dst) :=
 Grammar.drop_word active advance Control.done (by trivial) (block_path n vs len) v src scr dst

end RosserDirect.TypedBlock
