module
public import DirectContextProgramFormulas
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512

theorem agree_proofRow (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.proofRow q) = Routine.relocate rowRoles Control.proofRow (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]
theorem agree_proofCopy (q : FramedRowCopy.Control) (h : FramedRowCopy.machine q ≠ .halt) :
 machine (.proofCopy q) = Routine.relocate copyRoles Control.proofCopy (FramedRowCopy.machine q) := by
 cases q <;> simp_all [machine,FramedRowCopy.machine]
theorem agree_proofPrepare (q : FramedContext.Control) (h : FramedContext.prepare q ≠ .halt) :
 machine (.proofPrepare q) = Routine.relocate constructRoles Control.proofPrepare (FramedContext.prepare q) := by
 cases q <;> simp_all [machine,FramedContext.prepare]
theorem agree_proofMember (q : RosserDirect.Membership.Control) (h : RosserDirect.Membership.machine q ≠ .halt) :
 machine (.proofMember q) = Routine.relocate constructRoles Control.proofMember (RosserDirect.Membership.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.Membership.machine]

theorem embed_proofRow (q : FramedRowConstructor.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.proofRow (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.proofRow q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_proofCopy (q : FramedRowCopy.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed copyRoles Control.proofCopy (config q v rows scr vals) (storage p [] [] tmp []) =
 cfg (.proofCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_proofPrepare (q : FramedContext.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.proofPrepare (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.proofPrepare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_proofMember (q : RosserDirect.Membership.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.proofMember (RosserDirect.Membership.cfg q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.proofMember q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.Membership.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem proof_row_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
    (program rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.proofRow (.formula0 0)) v program (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg (.proofRow .done) none program (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective Control.proofRow
   (FramedRowConstructor.machine false) machine agree_proofRow (storage program [] [] [] [])
   (FramedRowConstructor.construct_seq Γ f v s rows) (by simp [config])
 simpa only [embed_proofRow] using h

theorem proof_copy_run (r : ZFR.Row) (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.proofCopy (.scan .tag)) v program vals [] [] (FramedRow.encode r ++ rows))
   (cfg (.proofCopy .done) none program (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows)) := by
 have h := Routine.lift_embedded_run copyRoles copy_injective Control.proofCopy
   FramedRowCopy.machine machine agree_proofCopy (storage program [] [] [] [])
   (FramedRowCopy.copy_row r v rows vals) (by simp [config])
 simpa only [embed_proofCopy] using h

theorem proof_prepare_run (Γ : ZFR.Context) (v : Option Symbol) (program src rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.proofPrepare .entry) v program (FramedContext.encode Γ ++ src) [] [] rows)
   (cfg (.proofPrepare .done) none program src [] (Membership.contextFrames Γ) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.proofPrepare
   FramedContext.prepare machine agree_proofPrepare (storage program [] [] [] rows)
   (FramedContext.prepare_membership Γ v src) (by simp [config])
 simpa only [embed_proofPrepare] using h

theorem proof_membership_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
    (program vals rows : List Symbol) :
 ∃ tmp, TM2.Reaches machine
   (cfg (.proofMember .next) v program (FramedRow.formulaFrame f ++ vals) [] (Membership.contextFrames Γ) rows)
   (cfg (.proofMember (if f ∈ Γ then .found else .absent)) none program (FramedRow.formulaFrame f ++ vals) [] tmp rows) := by
 obtain ⟨tmp,ht⟩ := Membership.lookup_context f Γ v vals
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.proofMember
   Membership.machine machine agree_proofMember (storage program [] [] [] rows) ht (by simp [Membership.cfg])
 refine ⟨tmp,?_⟩
 simpa [embed_proofMember,FramedRow.formulaFrame] using h



theorem agree_expCopy (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.expCopy q) = Routine.relocate constructRoles Control.expCopy (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem agree_expExpected (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.expExpected q) = Routine.relocate moveRoles Control.expExpected (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]
theorem agree_expCompare (q : FramedRowEquality.Control) (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.expCompare q) = Routine.relocate rowRoles Control.expCompare (FramedRowEquality.machine q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]
theorem agree_expResult (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.expResult q) = Routine.relocate rowRoles Control.expResult (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_expCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.expCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.expCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_expExpected (q : FramedRowConstructor.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.expExpected (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.expExpected q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_expCompare (q : FramedRowEquality.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.expCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.expCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_expResult (q : FramedRowConstructor.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.expResult (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.expResult q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem exp_copy_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
    (program rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.expCopy (.scan (.run 1 .start))) v program (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg (.expCopy .done) none program (TypedContext.stack (.formula f :: .context Γ :: s)) []
     (TypedContext.stack [.formula f,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.expCopy
   TypedBlock.machine machine agree_expCopy (storage program [] [] [] rows)
   (TypedBlock.copy_block 1 [.formula f,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_expCopy,TypedContext.stack,List.append_assoc] using h

theorem exp_expected_run (Γ : ZFR.Context) (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.expExpected (.formula0 0)) v program vals [] (TypedContext.stack [.formula .bot,.context Γ]) rows)
   (cfg (.expExpected .done) none program (FramedRow.encode (.seq Γ .bot) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.expExpected
   (FramedRowConstructor.machine false) machine agree_expExpected (storage program [] [] [] rows)
   (FramedRowConstructor.construct_seq Γ .bot v [] vals) (by simp [config])
 simpa [embed_expExpected,TypedContext.stack] using h

theorem exp_equal_run (r : ZFR.Row) (v : Option Symbol) (program vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
   (cfg (.expCompare .tag) v program (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows))
   (cfg (.expCompare .equal) w program vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.expCompare
   FramedRowEquality.machine machine agree_expCompare (storage program [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_expCompare] using h⟩

theorem exp_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (program vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
   (cfg (.expCompare .tag) v program (FramedRow.encode r ++ vals) [] [] (FramedRow.encode t ++ rows))
   (cfg (.expCompare .different) w program left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v vals [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run rowRoles row_injective Control.expCompare
   FramedRowEquality.machine machine agree_expCompare (storage program [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_expCompare] using h⟩

theorem exp_result_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
    (program rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.expResult (.formula0 0)) v program (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg (.expResult .done) none program (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective Control.expResult
   (FramedRowConstructor.machine false) machine agree_expResult (storage program [] [] [] [])
   (FramedRowConstructor.construct_seq Γ f v s rows) (by simp [config])
 simpa only [embed_expResult] using h

end RosserDirect.ContextProgram
