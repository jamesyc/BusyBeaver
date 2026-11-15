module
public import DirectRoutineRelabel
public import DirectTypedBlockDrop
@[expose] public section
namespace RosserDirect.SelectSecond
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | save (q : RosserDirect.Label)
 | drop (q : Grammar.DropControl TypedBlock.Control)
 | restore (q : RosserDirect.Label)
 | done
 deriving DecidableEq, Fintype, Inhabited

def swap : Stack → Stack
 | .input => .output | .scratch => .scratch | .output => .input

theorem swap_injective : Function.Injective swap := by intro a b h; cases a <;> cases b <;> simp_all [swap]

def machine : Control → Stmt Control
 | .save .done => .goto (fun _ => .drop (.scan (.run 0 .start)))
 | .save q => Routine.relocate id Control.save (RosserDirect.machine q)
 | .drop .done => .goto (fun _ => .restore .scan)
 | .drop q => Routine.relocate id Control.drop (TypedBlock.dropMachine q)
 | .restore .done => .goto (fun _ => .done)
 | .restore q => Routine.relocate swap Control.restore (RosserDirect.machine q)
 | .done => .halt

theorem agree_save (q : RosserDirect.Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.save q) = Routine.relocate id Control.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_drop (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.drop q) = Routine.relocate id Control.drop (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem agree_restore (q : RosserDirect.Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restore q) = Routine.relocate swap Control.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_save (q : RosserDirect.Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.save (RosserDirect.cfg q v a b c) (fun _ => []) = config (.save q) v a b c := by
 unfold Routine.embed RosserDirect.cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_drop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.drop (config q v a b c) (fun _ => []) = config (.drop q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_restore (q : RosserDirect.Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed swap Control.restore (RosserDirect.cfg q v a b c) (fun _ => []) = config (.restore q) v c b a := by
 unfold Routine.embed RosserDirect.cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Retain the top formula b, discard the next typed field a, preserve all
following fields and the other stack. This selects the second logical operand
because the assembler pushes arguments in left-to-right order. -/
theorem select_second (a : ZFR.TokenVM.Value) (b : ZFR.Formula) (v : Option Symbol)
 (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.save .scan) v (TypedContext.value (.formula b) ++ TypedContext.value a ++ src) [] dst)
 (config .done none (TypedContext.value (.formula b) ++ src) [] dst) := by
 have saveLocal := RosserDirect.move_frame (payloadBits (valueTokens (.formula b))) (payloadBits_no_end _) v (TypedContext.value a ++ src) dst
 have hs := Routine.lift_embedded_run id Function.injective_id Control.save RosserDirect.machine machine agree_save (fun _ => []) saveLocal (by simp [RosserDirect.cfg])
 simp only [embed_save] at hs
 have hl : TM2.Reaches machine
   (config (.save .done) none (TypedContext.value a ++ src) [] (TypedContext.value (.formula b) ++ dst))
   (config (.drop (.scan (.run 0 .start))) none (TypedContext.value a ++ src) [] (TypedContext.value (.formula b) ++ dst)) := Relation.ReflTransGen.single rfl
 obtain ⟨w,dropLocal⟩ := TypedBlock.drop_block 0 [a] rfl none src [] (TypedContext.value (.formula b) ++ dst)
 have hd := Routine.lift_embedded_run id Function.injective_id Control.drop TypedBlock.dropMachine machine agree_drop (fun _ => []) dropLocal (by simp [config])
 simp only [embed_drop] at hd
 have hdl : TM2.Reaches machine
   (config (.drop .done) w src [] (TypedContext.value (.formula b) ++ dst))
   (config (.restore .scan) w src [] (TypedContext.value (.formula b) ++ dst)) := Relation.ReflTransGen.single rfl
 have restoreLocal := RosserDirect.move_frame (payloadBits (valueTokens (.formula b))) (payloadBits_no_end _) w dst src
 have hr := Routine.lift_embedded_run swap swap_injective Control.restore RosserDirect.machine machine agree_restore (fun _ => []) restoreLocal (by simp [RosserDirect.cfg])
 simp only [embed_restore] at hr
 have hrl : TM2.Reaches machine
   (config (.restore .done) none (TypedContext.value (.formula b) ++ src) [] dst)
   (config .done none (TypedContext.value (.formula b) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   TypedContext.value,valueSymbols,List.append_assoc,List.singleton_append] at hs hl hd hdl hr hrl ⊢
 exact hs.trans (hl.trans (hd.trans (hdl.trans (hr.trans hrl))))

end RosserDirect.SelectSecond
