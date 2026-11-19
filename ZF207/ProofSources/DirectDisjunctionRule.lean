module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_diCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.diCopy q) = Routine.relocate constructRoles Control.diCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_diCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.diCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.diCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diDrop (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.diDrop q) = Routine.relocate moveRoles Control.diDrop ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_diDrop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.diDrop (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.diDrop q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diExpected (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.diExpected q) = Routine.relocate moveRoles Control.diExpected ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_diExpected (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.diExpected (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.diExpected q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diCompare (q : FramedRowEquality.Control) (h : (FramedRowEquality.machine) q ≠ .halt) :
 machine (.diCompare q) = Routine.relocate rowRoles Control.diCompare ((FramedRowEquality.machine) q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_diCompare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.diCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.diCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diBinary (q : RosserDirect.Binary.Control) (h : (RosserDirect.Binary.machine 9) q ≠ .halt) :
 machine (.diBinary q) = Routine.relocate constructRoles Control.diBinary ((RosserDirect.Binary.machine 9) q) := by
 cases q <;> simp_all [machine,RosserDirect.Binary.machine]

theorem embed_diBinary (q : RosserDirect.Binary.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.diBinary (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.diBinary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diMove (q : RosserDirect.Label) (h : (RosserDirect.machine) q ≠ .halt) :
 machine (.diMove q) = Routine.relocate moveRoles Control.diMove ((RosserDirect.machine) q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_diMove (q : RosserDirect.Label) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.diMove (RosserDirect.cfg q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.diMove q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_diResult (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.diResult q) = Routine.relocate rowRoles Control.diResult ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_diResult (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.diResult (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.diResult q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem di_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.diCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.diCopy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.diCopy
   TypedBlock.machine machine agree_diCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_diCopy,TypedContext.stack,List.append_assoc] using h

theorem di_drop_run (b : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.diDrop (.scan (.run 0 .start))) v p vals [] (TypedContext.value (.formula b) ++ tmp) rows)
 (cfg (.diDrop .done) w p vals [] tmp rows) := by
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.formula b] rfl v tmp [] vals
 have h := Routine.lift_embedded_run moveRoles move_injective Control.diDrop
   TypedBlock.dropMachine machine agree_diDrop (storage p [] [] [] rows) hw (by simp [config])
 exact ⟨w,by simpa [embed_diDrop,TypedContext.stack] using h⟩

theorem di_expected_run (Γ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.diExpected (.formula0 0)) v p vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
 (cfg (.diExpected .done) none p (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.diExpected
   (FramedRowConstructor.machine false) machine agree_diExpected (storage p [] [] [] rows)
   (FramedRowConstructor.construct_seq Γ a v [] vals) (by simp [config])
 simpa [embed_diExpected,TypedContext.stack] using h

theorem di_equal_run (r : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.diCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows))
 (cfg (.diCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.diCompare
   FramedRowEquality.machine machine agree_diCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_diCompare] using h⟩

theorem di_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.diCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode t ++ rows))
 (cfg (.diCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v vals [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run rowRoles row_injective Control.diCompare
   FramedRowEquality.machine machine agree_diCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_diCompare] using h⟩

theorem di_binary_run (a b : ZFR.Formula) (v : Option Symbol) (p src rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.diBinary .boot) v p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ src) [] [] rows)
 (cfg (.diBinary .done) none p src [] (TypedContext.value (.formula (.or a b))) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.diBinary
   (RosserDirect.Binary.machine 9) machine agree_diBinary (storage p [] [] [] rows)
   (binary_local 1 a b v src []) (by simp [config])
 simpa [embed_diBinary,binaryFormula] using h

theorem di_move_run (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.diMove .scan) v p vals [] (TypedContext.value (.formula a)) rows)
 (cfg (.diMove .done) none p (TypedContext.value (.formula a) ++ vals) [] [] rows) := by
 have localRun := RosserDirect.move_frame (payloadBits (valueTokens (.formula a))) (payloadBits_no_end _) v [] vals
 have h := Routine.lift_embedded_run moveRoles move_injective Control.diMove
   RosserDirect.machine machine agree_diMove (storage p [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_diMove,TypedContext.value,valueSymbols] using h

theorem di_result_run (Γ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.diResult (.formula0 0)) v p (TypedContext.stack (.formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.diResult .done) none p (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ a) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective Control.diResult
   (FramedRowConstructor.machine false) machine agree_diResult (storage p [] [] [] [])
   (FramedRowConstructor.construct_seq Γ a v s rows) (by simp [config])
 simpa only [embed_diResult] using h


theorem di_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 37 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.diCompare .tag) none rest (FramedRow.encode (.seq Γ a) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 18 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 18)) w rest vals [] [] rows)
   (cfg (.diCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := di_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diCopy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.diDrop (.scan (.run 0 .start))) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 obtain ⟨z,ht⟩ := di_drop_run b none rest vals (TypedContext.stack [.formula a,.context Γ]) rows
 have htl : TM2.Reaches machine
   (cfg (.diDrop .done) z rest vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
   (cfg (.diExpected (.formula0 0)) z rest vals [] (TypedContext.stack [.formula a,.context Γ]) rows) := global_step rfl
 have hx := di_expected_run Γ a z rest vals rows
 have hy : TM2.Reaches machine
   (cfg (.diExpected .done) none rest (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows)
   (cfg (.diCompare .tag) none rest (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := global_step rfl
 simp only [TM2.Reaches,vals,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hl ht htl hx hy ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (ht.trans (htl.trans (hx.trans hy))))))

theorem execute_di1 (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 37 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ a) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.or a b)) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.context Γ :: s)
 have ht := di_test_run Γ a b v rest (FramedRow.encode (.seq Γ a) ++ rows) s
 obtain ⟨w,he⟩ := di_equal_run (.seq Γ a) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.diCompare .equal) w rest vals [] [] rows)
   (cfg (.diBinary .boot) w rest vals [] [] rows) := global_step rfl
 have hb := di_binary_run a b w rest suffix rows
 have hbl : TM2.Reaches machine
   (cfg (.diBinary .done) none rest suffix [] (TypedContext.value (.formula (.or a b))) rows)
   (cfg (.diMove .scan) none rest suffix [] (TypedContext.value (.formula (.or a b))) rows) := global_step rfl
 have hm := di_move_run (.or a b) none rest suffix rows
 have hml : TM2.Reaches machine
   (cfg (.diMove .done) none rest (TypedContext.value (.formula (.or a b)) ++ suffix) [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest (TypedContext.value (.formula (.or a b)) ++ suffix) [] [] rows) := global_step rfl
 have hr := di_result_run Γ (.or a b) none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.or a b)) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.or a b)) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hb hbl hm hml hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hb.trans (hbl.trans (hm.trans (hml.trans (hr.trans hl)))))))

theorem reject_di1 (Γ : ZFR.Context) (a b : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ a ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 37 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := di_test_run Γ a b v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := di_different_run (.seq Γ a) actual hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.diCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
