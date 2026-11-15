module
public import DirectSelectSecond
public import DirectTypedBlockMove
@[expose] public section
namespace RosserDirect.OperandSwap
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | first (q : Grammar.CopyControl TypedBlock.Control)
 | second (q : Grammar.CopyControl TypedBlock.Control)
 | back (q : Grammar.CopyControl TypedBlock.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .first .done => .goto (fun _ => .second (.scan (.run 0 .start)))
 | .first q => Routine.relocate id Control.first (TypedBlock.moveMachine q)
 | .second .done => .goto (fun _ => .back (.scan (.run 1 .start)))
 | .second q => Routine.relocate id Control.second (TypedBlock.moveMachine q)
 | .back .done => .goto (fun _ => .done)
 | .back q => Routine.relocate SelectSecond.swap Control.back (TypedBlock.moveMachine q)
 | .done => .halt

theorem agree_first (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.first q) = Routine.relocate id Control.first (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_second (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.second q) = Routine.relocate id Control.second (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_back (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.back q) = Routine.relocate SelectSecond.swap Control.back (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_first (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.first (config q v a b c) (fun _ => []) = config (.first q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_second (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.second (config q v a b c) (fun _ => []) = config (.second q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_back (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.back (config q v a b c) (fun _ => []) = config (.back q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Swap arbitrary typed operands without changing their payloads or surrounding
stack tails, including contexts with multiple internal frame delimiters. -/
theorem swap_fields (a b : ZFR.TokenVM.Value) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.first (.scan (.run 0 .start))) v (TypedContext.value b ++ TypedContext.value a ++ src) [] dst)
 (config .done none (TypedContext.value a ++ TypedContext.value b ++ src) [] dst) := by
 have hf := Routine.lift_embedded_run id Function.injective_id Control.first
   TypedBlock.moveMachine machine agree_first (fun _ => [])
   (TypedBlock.move_block 0 [b] rfl v (TypedContext.value a ++ src) dst) (by simp [config])
 simp only [embed_first] at hf
 have hfl : TM2.Reaches machine
   (config (.first .done) none (TypedContext.value a ++ src) [] (TypedContext.value b ++ dst))
   (config (.second (.scan (.run 0 .start))) none (TypedContext.value a ++ src) [] (TypedContext.value b ++ dst)) := Relation.ReflTransGen.single rfl
 have hs := Routine.lift_embedded_run id Function.injective_id Control.second
   TypedBlock.moveMachine machine agree_second (fun _ => [])
   (TypedBlock.move_block 0 [a] rfl none src (TypedContext.value b ++ dst)) (by simp [config])
 simp only [embed_second] at hs
 have hsl : TM2.Reaches machine
   (config (.second .done) none src [] (TypedContext.value a ++ TypedContext.value b ++ dst))
   (config (.back (.scan (.run 1 .start))) none src [] (TypedContext.value a ++ TypedContext.value b ++ dst)) := Relation.ReflTransGen.single rfl
 have hb := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.back
   TypedBlock.moveMachine machine agree_back (fun _ => [])
   (TypedBlock.move_block 1 [a,b] rfl none dst src) (by simp [config])
 simp only [embed_back] at hb
 have hbl : TM2.Reaches machine
   (config (.back .done) none (TypedContext.value a ++ TypedContext.value b ++ src) [] dst)
   (config .done none (TypedContext.value a ++ TypedContext.value b ++ src) [] dst) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hf hfl hs hsl hb hbl ⊢
 exact hf.trans (hfl.trans (hs.trans (hsl.trans (hb.trans hbl))))

end RosserDirect.OperandSwap
