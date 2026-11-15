module
public import DirectSchemaRename
@[expose] public section
namespace RosserDirect.ReplacementBodies
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

def saveRoles : Stack → K
 | .input => .output | .scratch => .scratch | .output => .stream

theorem save_injective : Function.Injective saveRoles := by
 intro a b h; cases a <;> cases b <;> simp_all [saveRoles]

inductive Q where
 | duplicate (second : Bool) (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control))
 | renameA (q : SchemaRenameMachine.Q) | saveA (q : Label)
 | renameB (q : SchemaRenameMachine.Q) | saveB (q : Label)
 | renameC (q : SchemaRenameMachine.Q)
 | restorePair (q : Grammar.CopyControl TypedBlock.Control)
 | restoreC (q : Label) | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .duplicate false .done => .goto (fun _ => .duplicate true (.first (.scan (.run 0 .start))))
 | .duplicate true .done => .goto (fun _ => .renameA (.start 0))
 | .duplicate b q => Routine.relocate dataRoles (Q.duplicate b) (ReturnValue.duplicateMachine q)
 | .renameA .done => .goto (fun _ => .saveA .scan)
 | .renameA q => Routine.relocate id Q.renameA (SchemaRenameMachine.machine .replacementA q)
 | .saveA .done => .goto (fun _ => .renameB (.start 0))
 | .saveA q => Routine.relocate saveRoles Q.saveA (RosserDirect.machine q)
 | .renameB .done => .goto (fun _ => .saveB .scan)
 | .renameB q => Routine.relocate id Q.renameB (SchemaRenameMachine.machine .replacementB q)
 | .saveB .done => .goto (fun _ => .renameC (.start 0))
 | .saveB q => Routine.relocate saveRoles Q.saveB (RosserDirect.machine q)
 | .renameC .done => .goto (fun _ => .restorePair (.scan (.run 1 .start)))
 | .renameC q => Routine.relocate id Q.renameC (SchemaRenameMachine.machine .replacementC q)
 | .restorePair .done => .goto (fun _ => .restoreC .scan)
 | .restorePair q => Routine.relocate readRoles Q.restorePair (TypedBlock.moveMachine q)
 | .restoreC .done => .goto (fun _ => .done)
 | .restoreC q => Routine.relocate outputRoles Q.restoreC (RosserDirect.machine q)
 | .done => .halt

theorem agree_duplicate (b : Bool) (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control))
 (h : ReturnValue.duplicateMachine q ≠ .halt) :
 machine (.duplicate b q) = Routine.relocate dataRoles (Q.duplicate b) (ReturnValue.duplicateMachine q) := by
 cases q <;> cases b <;> simp_all [machine,ReturnValue.duplicateMachine,ReturnValue.machine]
theorem agree_A (q : SchemaRenameMachine.Q) (h : SchemaRenameMachine.machine .replacementA q ≠ .halt) :
 machine (.renameA q) = Routine.relocate id Q.renameA (SchemaRenameMachine.machine .replacementA q) := by
 cases q <;> simp_all [machine,SchemaRenameMachine.machine]
theorem agree_B (q : SchemaRenameMachine.Q) (h : SchemaRenameMachine.machine .replacementB q ≠ .halt) :
 machine (.renameB q) = Routine.relocate id Q.renameB (SchemaRenameMachine.machine .replacementB q) := by
 cases q <;> simp_all [machine,SchemaRenameMachine.machine]
theorem agree_C (q : SchemaRenameMachine.Q) (h : SchemaRenameMachine.machine .replacementC q ≠ .halt) :
 machine (.renameC q) = Routine.relocate id Q.renameC (SchemaRenameMachine.machine .replacementC q) := by
 cases q <;> simp_all [machine,SchemaRenameMachine.machine]
theorem agree_saveA (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.saveA q) = Routine.relocate saveRoles Q.saveA (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_saveB (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.saveB q) = Routine.relocate saveRoles Q.saveB (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_pair (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.restorePair q) = Routine.relocate readRoles Q.restorePair (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_restoreC (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restoreC q) = Routine.relocate outputRoles Q.restoreC (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_save (labels : Label → Q) (q : Label) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed saveRoles labels (config q v c s p) (fun _ => a) = cfg4 (labels q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev A (f : ZFR.Formula) := ZFR.rename ZFR.repAIndex f
abbrev B (f : ZFR.Formula) := ZFR.rename ZFR.repBIndex f
abbrev C (f : ZFR.Formula) := ZFR.rename ZFR.repCIndex f

theorem construct (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.duplicate false (.first (.scan (.run 0 .start)))) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .done none p (TypedContext.stack [.formula (C f),.formula (B f),.formula (A f)] ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective (Q.duplicate false)
  ReturnValue.duplicateMachine machine (agree_duplicate false) (fun _ => p)
  (ReturnValue.duplicate (.formula f) v a c) (by simp [config])
 simp only [embed_data] at h0
 have l0 : TM2.Reaches machine
  (cfg4 (.duplicate false .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.duplicate true (.first (.scan (.run 0 .start)))) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run dataRoles data_injective (Q.duplicate true)
  ReturnValue.duplicateMachine machine (agree_duplicate true) (fun _ => p)
  (ReturnValue.duplicate (.formula f) none (TypedContext.value (.formula f) ++ a) c) (by simp [config])
 simp only [embed_data] at h1
 have l1 : TM2.Reaches machine
  (cfg4 (.duplicate true .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.renameA (.start 0)) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := FourStack.relabel_run Q.renameA (SchemaRenameMachine.machine .replacementA) machine agree_A
  _ _ _ _ _ _ _ _ _ _ _ _ (SchemaRenameMachine.execute .replacementA f none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) c)
 have l2 : TM2.Reaches machine
  (cfg4 (.renameA .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] (TypedContext.value (.formula (A f)) ++ c))
  (cfg4 (.saveA .scan) none p (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] (TypedContext.value (.formula (A f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run saveRoles save_injective Q.saveA
  RosserDirect.machine machine agree_saveA (fun _ => TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a)
  (AllIntroPremise.move_formula (A f) none c p) (by simp [config])
 simp only [embed_save] at h3
 have l3 : TM2.Reaches machine
  (cfg4 (.saveA .done) none (TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.renameB (.start 0)) none (TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h4 := FourStack.relabel_run Q.renameB (SchemaRenameMachine.machine .replacementB) machine agree_B
  _ _ _ _ _ _ _ _ _ _ _ _ (SchemaRenameMachine.execute .replacementB f none (TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ a) c)
 have l4 : TM2.Reaches machine
  (cfg4 (.renameB .done) none (TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ a) [] (TypedContext.value (.formula (B f)) ++ c))
  (cfg4 (.saveB .scan) none (TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ a) [] (TypedContext.value (.formula (B f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run saveRoles save_injective Q.saveB
  RosserDirect.machine machine agree_saveB (fun _ => TypedContext.value (.formula f) ++ a)
  (AllIntroPremise.move_formula (B f) none c (TypedContext.value (.formula (A f)) ++ p)) (by simp [config])
 simp only [embed_save] at h5
 have l5 : TM2.Reaches machine
  (cfg4 (.saveB .done) none (TypedContext.value (.formula (B f)) ++ TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.renameC (.start 0)) none (TypedContext.value (.formula (B f)) ++ TypedContext.value (.formula (A f)) ++ p) (TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h6 := FourStack.relabel_run Q.renameC (SchemaRenameMachine.machine .replacementC) machine agree_C
  _ _ _ _ _ _ _ _ _ _ _ _ (SchemaRenameMachine.execute .replacementC f none (TypedContext.value (.formula (B f)) ++ TypedContext.value (.formula (A f)) ++ p) a c)
 have l6 : TM2.Reaches machine
  (cfg4 (.renameC .done) none (TypedContext.value (.formula (B f)) ++ TypedContext.value (.formula (A f)) ++ p) a [] (TypedContext.value (.formula (C f)) ++ c))
  (cfg4 (.restorePair (.scan (.run 1 .start))) none (TypedContext.value (.formula (B f)) ++ TypedContext.value (.formula (A f)) ++ p) a [] (TypedContext.value (.formula (C f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h7 := Routine.lift_embedded_run readRoles read_injective Q.restorePair
  TypedBlock.moveMachine machine agree_pair (fun _ => TypedContext.value (.formula (C f)) ++ c)
  (TypedBlock.move_block 1 [.formula (B f),.formula (A f)] rfl none p a) (by simp [config])
 simp only [embed_read] at h7
 have l7 : TM2.Reaches machine
  (cfg4 (.restorePair .done) none p (TypedContext.stack [.formula (B f),.formula (A f)] ++ a) [] (TypedContext.value (.formula (C f)) ++ c))
  (cfg4 (.restoreC .scan) none p (TypedContext.stack [.formula (B f),.formula (A f)] ++ a) [] (TypedContext.value (.formula (C f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h8 := Routine.lift_embedded_run outputRoles output_injective Q.restoreC
  RosserDirect.machine machine agree_restoreC (fun _ => p)
  (AllIntroPremise.move_formula (C f) none c (TypedContext.stack [.formula (B f),.formula (A f)] ++ a)) (by simp [config])
 simp only [embed_output] at h8
 have l8 : TM2.Reaches machine
  (cfg4 (.restoreC .done) none p (TypedContext.stack [.formula (C f),.formula (B f),.formula (A f)] ++ a) [] c)
  (cfg4 .done none p (TypedContext.stack [.formula (C f),.formula (B f),.formula (A f)] ++ a) [] c) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 h7 l7 h8 l8 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans (l6.trans (h7.trans (l7.trans (h8.trans l8))))))))))))))))

end RosserDirect.ReplacementBodies
