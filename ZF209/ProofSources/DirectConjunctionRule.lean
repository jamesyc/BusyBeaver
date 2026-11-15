module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_ceCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.ceCopy q) = Routine.relocate constructRoles Control.ceCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_ceCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ceCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ceCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ceDrop (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.ceDrop q) = Routine.relocate constructRoles Control.ceDrop ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_ceDrop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ceDrop (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ceDrop q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ceExpected (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.ceExpected q) = Routine.relocate moveRoles Control.ceExpected ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_ceExpected (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ceExpected (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ceExpected q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ceCompare (q : FramedRowEquality.Control) (h : (FramedRowEquality.machine) q ≠ .halt) :
 machine (.ceCompare q) = Routine.relocate rowRoles Control.ceCompare ((FramedRowEquality.machine) q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_ceCompare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.ceCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.ceCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ceBinary (q : RosserDirect.Binary.Control) (h : (RosserDirect.Binary.machine 7) q ≠ .halt) :
 machine (.ceBinary q) = Routine.relocate moveRoles Control.ceBinary ((RosserDirect.Binary.machine 7) q) := by
 cases q <;> simp_all [machine,RosserDirect.Binary.machine]

theorem embed_ceBinary (q : RosserDirect.Binary.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ceBinary (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ceBinary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ceMove (q : RosserDirect.Label) (h : (RosserDirect.machine) q ≠ .halt) :
 machine (.ceMove q) = Routine.relocate constructRoles Control.ceMove ((RosserDirect.machine) q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_ceMove (q : RosserDirect.Label) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ceMove (RosserDirect.cfg q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ceMove q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ce_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ceCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ceCopy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ceCopy
   TypedBlock.machine machine agree_ceCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_ceCopy,TypedContext.stack,List.append_assoc] using h

theorem ce_binary_run (a b : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ceBinary .boot) v p vals [] (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tmp) rows)
 (cfg (.ceBinary .done) none p (TypedContext.value (.formula (.and a b)) ++ vals) [] tmp rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ceBinary
   (RosserDirect.Binary.machine 7) machine agree_ceBinary (storage p [] [] [] rows)
   (binary_local 0 a b v tmp vals) (by simp [config])
 simpa [embed_ceBinary,binaryFormula] using h

theorem ce_move_run (a : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ceMove .scan) v p (TypedContext.value (.formula a) ++ vals) [] tmp rows)
 (cfg (.ceMove .done) none p vals [] (TypedContext.value (.formula a) ++ tmp) rows) := by
 have localRun := RosserDirect.move_frame (payloadBits (valueTokens (.formula a))) (payloadBits_no_end _) v vals tmp
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ceMove
   RosserDirect.machine machine agree_ceMove (storage p [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_ceMove,TypedContext.value,valueSymbols,List.append_assoc] using h

theorem ce_expected_run (Γ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ceExpected (.formula0 0)) v p vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
 (cfg (.ceExpected .done) none p (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ceExpected
   (FramedRowConstructor.machine false) machine agree_ceExpected (storage p [] [] [] rows)
   (FramedRowConstructor.construct_seq Γ a v [] vals) (by simp [config])
 simpa [embed_ceExpected,TypedContext.stack] using h

theorem ce_equal_run (r : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.ceCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows))
 (cfg (.ceCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ceCompare
   FramedRowEquality.machine machine agree_ceCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_ceCompare] using h⟩

theorem ce_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.ceCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode t ++ rows))
 (cfg (.ceCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v vals [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ceCompare
   FramedRowEquality.machine machine agree_ceCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_ceCompare] using h⟩

theorem ce_drop_run (b : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.ceDrop (.scan (.run 0 .start))) v p (TypedContext.value (.formula b) ++ vals) [] [] rows)
 (cfg (.ceDrop .done) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.formula b] rfl v vals [] []
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ceDrop
   TypedBlock.dropMachine machine agree_ceDrop (storage p [] [] [] rows) hw (by simp [config])
 exact ⟨w,by simpa [embed_ceDrop,TypedContext.stack] using h⟩


theorem ce_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 33 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ceCompare .tag) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let ctx := TypedContext.value (.context Γ)
 obtain ⟨w,hd⟩ := dispatch_run 16 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 16)) w rest vals [] [] rows)
   (cfg (.ceCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ce_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.ceCopy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.ceBinary .boot) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ce_binary_run a b none rest vals ctx rows
 have hbl : TM2.Reaches machine
   (cfg (.ceBinary .done) none rest (TypedContext.value (.formula (.and a b)) ++ vals) [] ctx rows)
   (cfg (.ceMove .scan) none rest (TypedContext.value (.formula (.and a b)) ++ vals) [] ctx rows) := global_step rfl
 have hm := ce_move_run (.and a b) none rest vals ctx rows
 have hml : TM2.Reaches machine
   (cfg (.ceMove .done) none rest vals [] (TypedContext.value (.formula (.and a b)) ++ ctx) rows)
   (cfg (.ceExpected (.formula0 0)) none rest vals [] (TypedContext.value (.formula (.and a b)) ++ ctx) rows) := global_step rfl
 have hx := ce_expected_run Γ (.and a b) none rest vals rows
 have hy : TM2.Reaches machine
   (cfg (.ceExpected .done) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ vals) [] [] rows)
   (cfg (.ceCompare .tag) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ vals) [] [] rows) := global_step rfl
 simp only [TM2.Reaches,vals,ctx,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hl hb hbl hm hml hx hy ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans (hbl.trans (hm.trans (hml.trans (hx.trans hy))))))))

theorem execute_ce1 (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 33 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ (.and a b)) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ a) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.formula a :: .context Γ :: s)
 have ht := ce_test_run Γ a b v rest (FramedRow.encode (.seq Γ (.and a b)) ++ rows) s
 obtain ⟨w,he⟩ := ce_equal_run (.seq Γ (.and a b)) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.ceCompare .equal) w rest vals [] [] rows)
   (cfg (.ceDrop (.scan (.run 0 .start))) w rest vals [] [] rows) := global_step rfl
 obtain ⟨z,hdrop⟩ := ce_drop_run b w rest suffix rows
 have hdl : TM2.Reaches machine (cfg (.ceDrop .done) z rest suffix [] [] rows)
   (cfg (.diResult (.formula0 0)) z rest suffix [] [] rows) := global_step rfl
 have hr := di_result_run Γ a z rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ a) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ a) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hdrop hdl hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hdrop.trans (hdl.trans (hr.trans hl)))))

theorem reject_ce1 (Γ : ZFR.Context) (a b : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ (.and a b) ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 33 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := ce_test_run Γ a b v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := ce_different_run (.seq Γ (.and a b)) actual hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.ceCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
