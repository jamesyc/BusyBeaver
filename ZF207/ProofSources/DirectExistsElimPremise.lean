module
public import DirectAllIntroPremise
@[expose] public section
namespace RosserDirect.ExistsElimPremise
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Q where
 | saveC (q : Label) | saveA (q : Label) | shiftContext (q : ShiftContext.Q)
 | backContext (q : Grammar.CopyControl TypedBlock.Control)
 | restoreA (q : Label) | swap (q : OperandSwap.Control) | cons (q : TypedContext.Control)
 | backExtended (q : Grammar.CopyControl TypedBlock.Control)
 | restoreC (q : Label) | shiftFormula (q : ShiftTraversal.Q)
 | backFormula (q : Label) | row (q : FramedRowConstructor.Control) | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .saveC .done => .goto (fun _ => .saveA .scan)
 | .saveC q => Routine.relocate prepareRoles Q.saveC (RosserDirect.machine q)
 | .saveA .done => .goto (fun _ => .shiftContext (.prepare .tag0))
 | .saveA q => Routine.relocate prepareRoles Q.saveA (RosserDirect.machine q)
 | .shiftContext .done => .goto (fun _ => .backContext (.scan (.run 0 .start)))
 | .shiftContext q => Routine.relocate id Q.shiftContext (ShiftContext.machine q)
 | .backContext .done => .goto (fun _ => .restoreA .scan)
 | .backContext q => Routine.relocate outputRoles Q.backContext (TypedBlock.moveMachine q)
 | .restoreA .done => .goto (fun _ => .swap (.first (.scan (.run 0 .start))))
 | .restoreA q => Routine.relocate readRoles Q.restoreA (RosserDirect.machine q)
 | .swap .done => .goto (fun _ => .cons .context0)
 | .swap q => Routine.relocate dataRoles Q.swap (OperandSwap.machine q)
 | .cons .done => .goto (fun _ => .backExtended (.scan (.run 0 .start)))
 | .cons q => Routine.relocate dataRoles Q.cons (TypedContext.machine q)
 | .backExtended .done => .goto (fun _ => .restoreC .scan)
 | .backExtended q => Routine.relocate outputRoles Q.backExtended (TypedBlock.moveMachine q)
 | .restoreC .done => .goto (fun _ => .shiftFormula (.prepare .formulaTag))
 | .restoreC q => Routine.relocate readRoles Q.restoreC (RosserDirect.machine q)
 | .shiftFormula .done => .goto (fun _ => .backFormula .scan)
 | .shiftFormula q => Routine.relocate id Q.shiftFormula (ShiftTraversal.machine q)
 | .backFormula .done => .goto (fun _ => .row (.formula0 0))
 | .backFormula q => Routine.relocate outputRoles Q.backFormula (RosserDirect.machine q)
 | .row .done => .goto (fun _ => .done)
 | .row q => Routine.relocate dataRoles Q.row (FramedRowConstructor.machine false q)
 | .done => .halt

theorem agree_saveC (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.saveC q) = Routine.relocate prepareRoles Q.saveC (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem agree_saveA (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.saveA q) = Routine.relocate prepareRoles Q.saveA (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem agree_shiftContext (q : ShiftContext.Q) (h : ShiftContext.machine q ≠ .halt) :
 machine (.shiftContext q) = Routine.relocate id Q.shiftContext (ShiftContext.machine q) := by
 cases q <;> simp_all [machine,ShiftContext.machine]

theorem agree_backContext (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.backContext q) = Routine.relocate outputRoles Q.backContext (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem agree_restoreA (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restoreA q) = Routine.relocate readRoles Q.restoreA (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem agree_swap (q : OperandSwap.Control) (h : OperandSwap.machine q ≠ .halt) :
 machine (.swap q) = Routine.relocate dataRoles Q.swap (OperandSwap.machine q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem agree_cons (q : TypedContext.Control) (h : TypedContext.machine q ≠ .halt) :
 machine (.cons q) = Routine.relocate dataRoles Q.cons (TypedContext.machine q) := by
 cases q <;> simp_all [machine,TypedContext.machine]

theorem agree_backExtended (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.backExtended q) = Routine.relocate outputRoles Q.backExtended (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem agree_restoreC (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restoreC q) = Routine.relocate readRoles Q.restoreC (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem agree_shiftFormula (q : ShiftTraversal.Q) (h : ShiftTraversal.machine q ≠ .halt) :
 machine (.shiftFormula q) = Routine.relocate id Q.shiftFormula (ShiftTraversal.machine q) := by
 cases q <;> simp_all [machine,ShiftTraversal.machine]

theorem agree_backFormula (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.backFormula q) = Routine.relocate outputRoles Q.backFormula (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem agree_row (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.row q) = Routine.relocate dataRoles Q.row ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]


/-- Exact second existential-elimination premise, including context and
conclusion shifts. Input is the VM's last-argument-first operand order. -/
theorem construct (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol) (p ds rs : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.saveC .scan) v p
    (TypedContext.value (.formula c) ++ TypedContext.value (.formula a) ++ TypedContext.value (.context Γ) ++ ds) [] rs)
  (cfg4 .done none p ds [] (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ rs)) := by
 let C := TypedContext.value (.formula c)
 let A := TypedContext.value (.formula a)
 let G := TypedContext.value (.context Γ)
 let S := TypedContext.value (.context (ZFR.shiftContext Γ))
 let E := TypedContext.value (.context (a :: ZFR.shiftContext Γ))
 let D := TypedContext.value (.formula (ZFR.shift c))
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.saveC
   RosserDirect.machine machine agree_saveC (fun _ => rs)
   (AllIntroPremise.move_formula c v (A ++ G ++ ds) p) (by simp [config])
 simp only [embed_prepare] at h0
 have l0 : TM2.Reaches machine
   (cfg4 (.saveC .done) none (C ++ p) (A ++ G ++ ds) [] rs)
   (cfg4 (.saveA .scan) none (C ++ p) (A ++ G ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run prepareRoles prepare_injective Q.saveA
   RosserDirect.machine machine agree_saveA (fun _ => rs)
   (AllIntroPremise.move_formula a none (G ++ ds) (C ++ p)) (by simp [config])
 simp only [embed_prepare] at h1
 have l1 : TM2.Reaches machine
   (cfg4 (.saveA .done) none (A ++ C ++ p) (G ++ ds) [] rs)
   (cfg4 (.shiftContext (.prepare .tag0)) none (A ++ C ++ p) (G ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h2 := FourStack.relabel_run Q.shiftContext ShiftContext.machine machine agree_shiftContext
   _ _ _ _ _ _ _ _ _ _ _ _ (ShiftContext.shift_context Γ none (A ++ C ++ p) ds rs)
 have l2 : TM2.Reaches machine
   (cfg4 (.shiftContext .done) none (A ++ C ++ p) ds [] (S ++ rs))
   (cfg4 (.backContext (.scan (.run 0 .start))) none (A ++ C ++ p) ds [] (S ++ rs)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run outputRoles output_injective Q.backContext
   TypedBlock.moveMachine machine agree_backContext (fun _ => A ++ C ++ p)
   (TypedBlock.move_block 0 [.context (ZFR.shiftContext Γ)] rfl none rs ds) (by simp [config])
 simp only [embed_output,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h3
 have l3 : TM2.Reaches machine
   (cfg4 (.backContext .done) none (A ++ C ++ p) (S ++ ds) [] rs)
   (cfg4 (.restoreA .scan) none (A ++ C ++ p) (S ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run readRoles read_injective Q.restoreA
   RosserDirect.machine machine agree_restoreA (fun _ => rs)
   (AllIntroPremise.move_formula a none (C ++ p) (S ++ ds)) (by simp [config])
 simp only [embed_read] at h4
 have l4 : TM2.Reaches machine
   (cfg4 (.restoreA .done) none (C ++ p) (A ++ S ++ ds) [] rs)
   (cfg4 (.swap (.first (.scan (.run 0 .start)))) none (C ++ p) (A ++ S ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run dataRoles data_injective Q.swap
   OperandSwap.machine machine agree_swap (fun _ => C ++ p)
   (OperandSwap.swap_fields (.context (ZFR.shiftContext Γ)) (.formula a) none ds rs) (by simp [config])
 simp only [embed_data] at h5
 have l5 : TM2.Reaches machine
   (cfg4 (.swap .done) none (C ++ p) (S ++ A ++ ds) [] rs)
   (cfg4 (.cons .context0) none (C ++ p) (S ++ A ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h6 := Routine.lift_embedded_run dataRoles data_injective Q.cons
   TypedContext.machine machine agree_cons (fun _ => C ++ p)
   (ImpIntroPremise.cons_raw a (ZFR.shiftContext Γ) none ds rs) (by simp [config])
 simp only [embed_data] at h6
 have l6 : TM2.Reaches machine
   (cfg4 (.cons .done) none (C ++ p) ds [] (E ++ rs))
   (cfg4 (.backExtended (.scan (.run 0 .start))) none (C ++ p) ds [] (E ++ rs)) := Relation.ReflTransGen.single rfl
 have h7 := Routine.lift_embedded_run outputRoles output_injective Q.backExtended
   TypedBlock.moveMachine machine agree_backExtended (fun _ => C ++ p)
   (TypedBlock.move_block 0 [.context (a :: ZFR.shiftContext Γ)] rfl none rs ds) (by simp [config])
 simp only [embed_output,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h7
 have l7 : TM2.Reaches machine
   (cfg4 (.backExtended .done) none (C ++ p) (E ++ ds) [] rs)
   (cfg4 (.restoreC .scan) none (C ++ p) (E ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h8 := Routine.lift_embedded_run readRoles read_injective Q.restoreC
   RosserDirect.machine machine agree_restoreC (fun _ => rs)
   (AllIntroPremise.move_formula c none p (E ++ ds)) (by simp [config])
 simp only [embed_read] at h8
 have l8 : TM2.Reaches machine
   (cfg4 (.restoreC .done) none p (C ++ E ++ ds) [] rs)
   (cfg4 (.shiftFormula (.prepare .formulaTag)) none p (C ++ E ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h9 := FourStack.relabel_run Q.shiftFormula ShiftTraversal.machine machine agree_shiftFormula
   _ _ _ _ _ _ _ _ _ _ _ _ (ShiftTraversal.shift_formula c none p (E ++ ds) rs)
 have l9 : TM2.Reaches machine
   (cfg4 (.shiftFormula .done) none p (E ++ ds) [] (D ++ rs))
   (cfg4 (.backFormula .scan) none p (E ++ ds) [] (D ++ rs)) := Relation.ReflTransGen.single rfl
 have h10 := Routine.lift_embedded_run outputRoles output_injective Q.backFormula
   RosserDirect.machine machine agree_backFormula (fun _ => p)
   (AllIntroPremise.move_formula (ZFR.shift c) none rs (E ++ ds)) (by simp [config])
 simp only [embed_output] at h10
 have l10 : TM2.Reaches machine
   (cfg4 (.backFormula .done) none p (D ++ E ++ ds) [] rs)
   (cfg4 (.row (.formula0 0)) none p (D ++ E ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h11 := Routine.lift_embedded_run dataRoles data_injective Q.row
   (FramedRowConstructor.machine false) machine agree_row (fun _ => p)
   (FramedRowConstructor.construct_seq_raw (a :: ZFR.shiftContext Γ) (ZFR.shift c) none ds rs) (by simp [config])
 simp only [embed_data] at h11
 have l11 : TM2.Reaches machine
   (cfg4 (.row .done) none p ds [] (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ rs))
   (cfg4 .done none p ds [] (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ rs)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 h7 l7 h8 l8 h9 l9 h10 l10 h11 l11 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans (l6.trans (h7.trans (l7.trans (h8.trans (l8.trans (h9.trans (l9.trans (h10.trans (l10.trans (h11.trans l11))))))))))))))))))))))

end RosserDirect.ExistsElimPremise
