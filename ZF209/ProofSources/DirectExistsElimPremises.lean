module
public import DirectExistsElimPremise
@[expose] public section
namespace RosserDirect.ExistsElimPremises
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Q where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | drop (q : Grammar.DropControl TypedBlock.Control)
 | makeEx (q : Label) | backEx (q : Label) | firstRow (q : FramedRowConstructor.Control)
 | restore (q : Grammar.CopyControl TypedBlock.Control)
 | second (q : ExistsElimPremise.Q) | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .copy .done => .goto (fun _ => .drop (.scan (.run 0 .start)))
 | .copy q => Routine.relocate prepareRoles Q.copy (TypedBlock.machine q)
 | .drop .done => .goto (fun _ => .makeEx .scan)
 | .drop q => Routine.relocate dataRoles Q.drop (TypedBlock.dropMachine q)
 | .makeEx .done => .goto (fun _ => .backEx .scan)
 | .makeEx q => Routine.relocate dataRoles Q.makeEx (Append.machine (tokenBits 15) q)
 | .backEx .done => .goto (fun _ => .firstRow (.formula0 0))
 | .backEx q => Routine.relocate outputRoles Q.backEx (RosserDirect.machine q)
 | .firstRow .done => .goto (fun _ => .restore (.scan (.run 2 .start)))
 | .firstRow q => Routine.relocate dataRoles Q.firstRow (FramedRowConstructor.machine false q)
 | .restore .done => .goto (fun _ => .second (.saveC .scan))
 | .restore q => Routine.relocate readRoles Q.restore (TypedBlock.moveMachine q)
 | .second .done => .goto (fun _ => .done)
 | .second q => Routine.relocate id Q.second (ExistsElimPremise.machine q)
 | .done => .halt

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.copy q) = Routine.relocate prepareRoles Q.copy (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem agree_drop (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.drop q) = Routine.relocate dataRoles Q.drop (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem agree_makeEx (q : Label) (h : Append.machine (tokenBits 15) q ≠ .halt) :
 machine (.makeEx q) = Routine.relocate dataRoles Q.makeEx (Append.machine (tokenBits 15) q) := by
 cases q <;> simp_all [machine,Append.machine]
theorem agree_backEx (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.backEx q) = Routine.relocate outputRoles Q.backEx (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_firstRow (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.firstRow q) = Routine.relocate dataRoles Q.firstRow (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]
theorem agree_restore (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.restore q) = Routine.relocate readRoles Q.restore (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_second (q : ExistsElimPremise.Q) (h : ExistsElimPremise.machine q ≠ .halt) :
 machine (.second q) = Routine.relocate id Q.second (ExistsElimPremise.machine q) := by
 cases q <;> simp_all [machine,ExistsElimPremise.machine]

theorem make_ex (a : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (Append.machine (tokenBits 15))
  (config Label.scan v (TypedContext.value (.formula a) ++ src) [] dst)
  (config Label.done none src [] (TypedContext.value (.formula (.ex a)) ++ dst)) := by
 simpa [TM2.Reaches,cfg,config,TypedContext.value,valueSymbols,valueTokens,ZFR.TokenVM.emitFormula,
   payloadBits,List.flatMap_append,List.append_assoc] using
   Append.append_frame (tokenBits 15) (payloadBits (valueTokens (.formula a))) (payloadBits_no_end _) v src dst

/-- Exact expected premise pair in the checker's stack order: second premise
above first. Produces no guessed rows and preserves all four surrounding tails. -/
theorem construct (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol) (p ds rs : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.copy (.scan (.run 2 .start))) v p
    (TypedContext.value (.formula c) ++ TypedContext.value (.formula a) ++ TypedContext.value (.context Γ) ++ ds) [] rs)
  (cfg4 .done none p ds []
    (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ FramedRow.encode (.seq Γ (.ex a)) ++ rs)) := by
 let V := TypedContext.stack [.formula c,.formula a,.context Γ]
 let A := TypedContext.value (.formula a)
 let G := TypedContext.value (.context Γ)
 let E := TypedContext.value (.formula (.ex a))
 let R := FramedRow.encode (.seq Γ (.ex a))
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.copy
   TypedBlock.machine machine agree_copy (fun _ => rs)
   (TypedBlock.copy_block 2 [.formula c,.formula a,.context Γ] rfl v ds p) (by simp [config])
 simp only [embed_prepare] at h0
 have l0 : TM2.Reaches machine
   (cfg4 (.copy .done) none (V ++ p) (V ++ ds) [] rs)
   (cfg4 (.drop (.scan (.run 0 .start))) none (V ++ p) (V ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.formula c] rfl none (A ++ G ++ ds) [] rs
 have h1 := Routine.lift_embedded_run dataRoles data_injective Q.drop
   TypedBlock.dropMachine machine agree_drop (fun _ => V ++ p) hw (by simp [config])
 simp only [embed_data] at h1
 have l1 : TM2.Reaches machine
   (cfg4 (.drop .done) w (V ++ p) (A ++ G ++ ds) [] rs)
   (cfg4 (.makeEx .scan) w (V ++ p) (A ++ G ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run dataRoles data_injective Q.makeEx
   (Append.machine (tokenBits 15)) machine agree_makeEx (fun _ => V ++ p)
   (make_ex a w (G ++ ds) rs) (by simp [config])
 simp only [embed_data] at h2
 have l2 : TM2.Reaches machine
   (cfg4 (.makeEx .done) none (V ++ p) (G ++ ds) [] (E ++ rs))
   (cfg4 (.backEx .scan) none (V ++ p) (G ++ ds) [] (E ++ rs)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run outputRoles output_injective Q.backEx
   RosserDirect.machine machine agree_backEx (fun _ => V ++ p)
   (AllIntroPremise.move_formula (.ex a) none rs (G ++ ds)) (by simp [config])
 simp only [embed_output] at h3
 have l3 : TM2.Reaches machine
   (cfg4 (.backEx .done) none (V ++ p) (E ++ G ++ ds) [] rs)
   (cfg4 (.firstRow (.formula0 0)) none (V ++ p) (E ++ G ++ ds) [] rs) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run dataRoles data_injective Q.firstRow
   (FramedRowConstructor.machine false) machine agree_firstRow (fun _ => V ++ p)
   (FramedRowConstructor.construct_seq_raw Γ (.ex a) none ds rs) (by simp [config])
 simp only [embed_data] at h4
 have l4 : TM2.Reaches machine
   (cfg4 (.firstRow .done) none (V ++ p) ds [] (R ++ rs))
   (cfg4 (.restore (.scan (.run 2 .start))) none (V ++ p) ds [] (R ++ rs)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run readRoles read_injective Q.restore
   TypedBlock.moveMachine machine agree_restore (fun _ => R ++ rs)
   (TypedBlock.move_block 2 [.formula c,.formula a,.context Γ] rfl none p ds) (by simp [config])
 simp only [embed_read] at h5
 have l5 : TM2.Reaches machine
   (cfg4 (.restore .done) none p (V ++ ds) [] (R ++ rs))
   (cfg4 (.second (.saveC .scan)) none p (V ++ ds) [] (R ++ rs)) := Relation.ReflTransGen.single rfl
 have h6 := FourStack.relabel_run Q.second ExistsElimPremise.machine machine agree_second
   _ _ _ _ _ _ _ _ _ _ _ _ (ExistsElimPremise.construct Γ a c none p ds (R ++ rs))
 have l6 : TM2.Reaches machine
   (cfg4 (.second .done) none p ds [] (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ R ++ rs))
   (cfg4 .done none p ds [] (FramedRow.encode (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) ++ R ++ rs)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,V,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans l6))))))))))))

end RosserDirect.ExistsElimPremises
