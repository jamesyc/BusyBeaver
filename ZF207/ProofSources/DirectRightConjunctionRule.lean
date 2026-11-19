module
public import DirectRightDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_ce2Copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.ce2Copy q) = Routine.relocate constructRoles Control.ce2Copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_ce2Copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ce2Copy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ce2Copy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ce2Expected (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.ce2Expected q) = Routine.relocate moveRoles Control.ce2Expected ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_ce2Expected (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ce2Expected (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ce2Expected q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ce2Compare (q : FramedRowEquality.Control) (h : (FramedRowEquality.machine) q ≠ .halt) :
 machine (.ce2Compare q) = Routine.relocate rowRoles Control.ce2Compare ((FramedRowEquality.machine) q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_ce2Compare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.ce2Compare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.ce2Compare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ce2Binary (q : RosserDirect.Binary.Control) (h : (RosserDirect.Binary.machine 7) q ≠ .halt) :
 machine (.ce2Binary q) = Routine.relocate moveRoles Control.ce2Binary ((RosserDirect.Binary.machine 7) q) := by
 cases q <;> simp_all [machine,RosserDirect.Binary.machine]

theorem embed_ce2Binary (q : RosserDirect.Binary.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ce2Binary (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ce2Binary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ce2Move (q : RosserDirect.Label) (h : (RosserDirect.machine) q ≠ .halt) :
 machine (.ce2Move q) = Routine.relocate constructRoles Control.ce2Move ((RosserDirect.machine) q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_ce2Move (q : RosserDirect.Label) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ce2Move (RosserDirect.cfg q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ce2Move q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ce2_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ce2Copy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ce2Copy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ce2Copy
   TypedBlock.machine machine agree_ce2Copy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_ce2Copy,TypedContext.stack,List.append_assoc] using h

theorem ce2_binary_run (a b : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ce2Binary .boot) v p vals [] (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tmp) rows)
 (cfg (.ce2Binary .done) none p (TypedContext.value (.formula (.and a b)) ++ vals) [] tmp rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ce2Binary
   (RosserDirect.Binary.machine 7) machine agree_ce2Binary (storage p [] [] [] rows)
   (binary_local 0 a b v tmp vals) (by simp [config])
 simpa [embed_ce2Binary,binaryFormula] using h

theorem ce2_move_run (a : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ce2Move .scan) v p (TypedContext.value (.formula a) ++ vals) [] tmp rows)
 (cfg (.ce2Move .done) none p vals [] (TypedContext.value (.formula a) ++ tmp) rows) := by
 have localRun := RosserDirect.move_frame (payloadBits (valueTokens (.formula a))) (payloadBits_no_end _) v vals tmp
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ce2Move
   RosserDirect.machine machine agree_ce2Move (storage p [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_ce2Move,TypedContext.value,valueSymbols,List.append_assoc] using h

theorem ce2_expected_run (Γ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ce2Expected (.formula0 0)) v p vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
 (cfg (.ce2Expected .done) none p (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ce2Expected
   (FramedRowConstructor.machine false) machine agree_ce2Expected (storage p [] [] [] rows)
   (FramedRowConstructor.construct_seq Γ a v [] vals) (by simp [config])
 simpa [embed_ce2Expected,TypedContext.stack] using h

theorem ce2_equal_run (r : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.ce2Compare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows))
 (cfg (.ce2Compare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ce2Compare
   FramedRowEquality.machine machine agree_ce2Compare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_ce2Compare] using h⟩

theorem ce2_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.ce2Compare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode t ++ rows))
 (cfg (.ce2Compare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v vals [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ce2Compare
   FramedRowEquality.machine machine agree_ce2Compare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_ce2Compare] using h⟩

theorem agree_ce2Select (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.ce2Select q) = Routine.relocate constructRoles Control.ce2Select (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_ce2Select (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ce2Select (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ce2Select q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ce2_select_run (a b : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ce2Select (.save .scan)) v p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ vals) [] [] rows)
 (cfg (.ce2Select .done) none p (TypedContext.value (.formula b) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ce2Select
   SelectSecond.machine machine agree_ce2Select (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) b v vals []) (by simp [config])
 simpa only [embed_ce2Select] using h

theorem ce2_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 35 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ce2Compare .tag) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let ctx := TypedContext.value (.context Γ)
 obtain ⟨w,hd⟩ := dispatch_run 17 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 17)) w rest vals [] [] rows)
   (cfg (.ce2Copy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ce2_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.ce2Copy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.ce2Binary .boot) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ce2_binary_run a b none rest vals ctx rows
 have hbl : TM2.Reaches machine
   (cfg (.ce2Binary .done) none rest (TypedContext.value (.formula (.and a b)) ++ vals) [] ctx rows)
   (cfg (.ce2Move .scan) none rest (TypedContext.value (.formula (.and a b)) ++ vals) [] ctx rows) := global_step rfl
 have hm := ce2_move_run (.and a b) none rest vals ctx rows
 have hml : TM2.Reaches machine
   (cfg (.ce2Move .done) none rest vals [] (TypedContext.value (.formula (.and a b)) ++ ctx) rows)
   (cfg (.ce2Expected (.formula0 0)) none rest vals [] (TypedContext.value (.formula (.and a b)) ++ ctx) rows) := global_step rfl
 have hx := ce2_expected_run Γ (.and a b) none rest vals rows
 have hy : TM2.Reaches machine
   (cfg (.ce2Expected .done) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ vals) [] [] rows)
   (cfg (.ce2Compare .tag) none rest (FramedRow.encode (.seq Γ (.and a b)) ++ vals) [] [] rows) := global_step rfl
 simp only [TM2.Reaches,vals,ctx,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hl hb hbl hm hml hx hy ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans (hbl.trans (hm.trans (hml.trans (hx.trans hy))))))))

theorem execute_ce2 (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 35 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ (.and a b)) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.formula b :: .context Γ :: s)
 have ht := ce2_test_run Γ a b v rest (FramedRow.encode (.seq Γ (.and a b)) ++ rows) s
 obtain ⟨w,he⟩ := ce2_equal_run (.seq Γ (.and a b)) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.ce2Compare .equal) w rest vals [] [] rows)
   (cfg (.ce2Select (.save .scan)) w rest vals [] [] rows) := global_step rfl
 have hselect := ce2_select_run a b w rest (TypedContext.stack (.context Γ :: s)) rows
 have hsl : TM2.Reaches machine (cfg (.ce2Select .done) none rest suffix [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest suffix [] [] rows) := global_step rfl
 have hr := di_result_run Γ b none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hselect hsl hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hselect.trans (hsl.trans (hr.trans hl)))))

theorem reject_ce2 (Γ : ZFR.Context) (a b : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ (.and a b) ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 35 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := ce2_test_run Γ a b v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := ce2_different_run (.seq Γ (.and a b)) actual hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.ce2Compare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
