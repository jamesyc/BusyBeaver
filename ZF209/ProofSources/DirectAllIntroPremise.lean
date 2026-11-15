module
public import DirectShiftContext
public import DirectRawPremiseBuilder
@[expose] public section
namespace RosserDirect.AllIntroPremise
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Q where
 | save (q : Label) | shift (q : ShiftContext.Q)
 | backContext (q : Grammar.CopyControl TypedBlock.Control)
 | restore (q : Label) | row (q : FramedRowConstructor.Control) | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .save .done => .goto (fun _ => .shift (.prepare .tag0))
 | .save q => Routine.relocate prepareRoles Q.save (RosserDirect.machine q)
 | .shift .done => .goto (fun _ => .backContext (.scan (.run 0 .start)))
 | .shift q => Routine.relocate id Q.shift (ShiftContext.machine q)
 | .backContext .done => .goto (fun _ => .restore .scan)
 | .backContext q => Routine.relocate outputRoles Q.backContext (TypedBlock.moveMachine q)
 | .restore .done => .goto (fun _ => .row (.formula0 0))
 | .restore q => Routine.relocate readRoles Q.restore (RosserDirect.machine q)
 | .row .done => .goto (fun _ => .done)
 | .row q => Routine.relocate dataRoles Q.row (FramedRowConstructor.machine false q)
 | .done => .halt

theorem agree_save (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.save q) = Routine.relocate prepareRoles Q.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_shift (q : ShiftContext.Q) (h : ShiftContext.machine q ≠ .halt) :
 machine (.shift q) = Routine.relocate id Q.shift (ShiftContext.machine q) := by
 cases q <;> simp_all [machine,ShiftContext.machine]
theorem agree_backContext (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.backContext q) = Routine.relocate outputRoles Q.backContext (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_restore (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restore q) = Routine.relocate readRoles Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_row (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.row q) = Routine.relocate dataRoles Q.row (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem move_formula (f : ZFR.Formula) (v : Option Symbol) (a c : List Symbol) :
 TM2.Reaches RosserDirect.machine (config Label.scan v (TypedContext.value (.formula f) ++ a) [] c)
  (config Label.done none a [] (TypedContext.value (.formula f) ++ c)) := by
 simpa [TM2.Reaches,cfg,config,TypedContext.value,valueSymbols,List.append_assoc] using
   RosserDirect.move_frame (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) v a c

/-- Construct the exact universal-introduction premise Γ↑ ⊢ a from canonical
formula/context operands. Uses only four finite stack roles and preserves tails. -/
theorem construct (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ a) [] c)
  (cfg4 .done none p a [] (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.save
   RosserDirect.machine machine agree_save (fun _ => c)
   (move_formula f v (TypedContext.value (.context Γ) ++ a) p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.save .done) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.context Γ) ++ a) [] c)
   (cfg4 (.shift (.prepare .tag0)) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.context Γ) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := FourStack.relabel_run Q.shift ShiftContext.machine machine agree_shift
   _ _ _ _ _ _ _ _ _ _ _ _ (ShiftContext.shift_context Γ none (TypedContext.value (.formula f) ++ p) a c)
 have h3 : TM2.Reaches machine
   (cfg4 (.shift .done) none (TypedContext.value (.formula f) ++ p) a [] (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ c))
   (cfg4 (.backContext (.scan (.run 0 .start))) none (TypedContext.value (.formula f) ++ p) a [] (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ c)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run outputRoles output_injective Q.backContext
   TypedBlock.moveMachine machine agree_backContext (fun _ => TypedContext.value (.formula f) ++ p)
   (TypedBlock.move_block 0 [.context (ZFR.shiftContext Γ)] rfl none c a) (by simp [config])
 simp only [embed_output,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h4
 have h5 : TM2.Reaches machine
   (cfg4 (.backContext .done) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ a) [] c)
   (cfg4 (.restore .scan) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h6 := Routine.lift_embedded_run readRoles read_injective Q.restore
   RosserDirect.machine machine agree_restore (fun _ => c)
   (move_formula f none p (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ a)) (by simp [config])
 simp only [embed_read] at h6
 have h7 : TM2.Reaches machine
   (cfg4 (.restore .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.context (ZFR.shiftContext Γ)) ++ a) [] c)
   (cfg4 (.row (.formula0 0)) none p (TypedContext.value (.formula f) ++ TypedContext.value (.context (ZFR.shiftContext Γ)) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h8 := Routine.lift_embedded_run dataRoles data_injective Q.row
   (FramedRowConstructor.machine false) machine agree_row (fun _ => p)
   (FramedRowConstructor.construct_seq_raw (ZFR.shiftContext Γ) f none a c) (by simp [config])
 simp only [embed_data] at h8
 have h9 : TM2.Reaches machine
   (cfg4 (.row .done) none p a [] (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ c))
   (cfg4 .done none p a [] (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ c)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
 exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans h9))))))))

end RosserDirect.AllIntroPremise
