module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_wkCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.wkCopy q) = Routine.relocate constructRoles Control.wkCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_wkCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.wkCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.wkCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkSelect (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.wkSelect q) = Routine.relocate moveRoles Control.wkSelect ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_wkSelect (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.wkSelect (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.wkSelect q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkExpected (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.wkExpected q) = Routine.relocate moveRoles Control.wkExpected ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_wkExpected (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.wkExpected (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.wkExpected q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkCompare (q : FramedRowEquality.Control) (h : (FramedRowEquality.machine) q ≠ .halt) :
 machine (.wkCompare q) = Routine.relocate rowRoles Control.wkCompare ((FramedRowEquality.machine) q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_wkCompare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.wkCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.wkCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkCheck (q : WeakeningContextCheck.Control) (h : (WeakeningContextCheck.machine) q ≠ .halt) :
 machine (.wkCheck q) = Routine.relocate constructRoles Control.wkCheck ((WeakeningContextCheck.machine) q) := by
 cases q <;> simp_all [machine,WeakeningContextCheck.machine]

theorem embed_wkCheck (q : WeakeningContextCheck.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.wkCheck (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.wkCheck q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkResult (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.wkResult q) = Routine.relocate rowRoles Control.wkResult ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_wkResult (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.wkResult (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.wkResult q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_wkDrop (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.wkDrop q) = Routine.relocate constructRoles Control.wkDrop ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_wkDrop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.wkDrop (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.wkDrop q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem wk_copy_run (Γ Δ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.wkCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows)
 (cfg (.wkCopy .done) none p (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] (TypedContext.stack [.formula a,.context Δ,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.wkCopy
   TypedBlock.machine machine agree_wkCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula a,.context Δ,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_wkCopy,TypedContext.stack,List.append_assoc] using h

theorem wk_select_run (Γ Δ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.wkSelect (.save .scan)) v p vals [] (TypedContext.stack [.formula a,.context Δ,.context Γ]) rows)
 (cfg (.wkSelect .done) none p vals [] (TypedContext.stack [.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.wkSelect
   SelectSecond.machine machine agree_wkSelect (storage p [] [] [] rows)
   (SelectSecond.select_second (.context Δ) a v (TypedContext.value (.context Γ)) vals) (by simp [config])
 simpa [embed_wkSelect,TypedContext.stack] using h

theorem wk_expected_run (Γ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.wkExpected (.formula0 0)) v p vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
 (cfg (.wkExpected .done) none p (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.wkExpected
   (FramedRowConstructor.machine false) machine agree_wkExpected (storage p [] [] [] rows)
   (FramedRowConstructor.construct_seq Γ a v [] vals) (by simp [config])
 simpa [embed_wkExpected,TypedContext.stack] using h

theorem wk_equal_run (r : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.wkCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode r ++ rows))
 (cfg (.wkCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.wkCompare
   FramedRowEquality.machine machine agree_wkCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_wkCompare] using h⟩

theorem wk_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.wkCompare .tag) v p (FramedRow.encode r ++ vals) [] [] (FramedRow.encode t ++ rows))
 (cfg (.wkCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v vals [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run rowRoles row_injective Control.wkCompare
   FramedRowEquality.machine machine agree_wkCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_wkCompare] using h⟩

theorem wk_check_run (Γ Δ : ZFR.Context) (a : ZFR.Formula) (sub : ∀ f ∈ Γ, f ∈ Δ)
 (v : Option Symbol) (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.wkCheck (.copy (.scan (.run 2 .start)))) v p (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows)
 (cfg (.wkCheck .accept) none p (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.wkCheck
   WeakeningContextCheck.machine machine agree_wkCheck (storage p [] [] [] rows)
   (WeakeningContextCheck.accepts Γ Δ a sub v (TypedContext.stack s)) (by simp [config])
 simpa [embed_wkCheck,WeakeningContextCheck.args,TypedContext.stack,List.append_assoc] using h

theorem wk_check_reject (Γ Δ : ZFR.Context) (a : ZFR.Formula) (nsub : ¬(∀ f ∈ Γ, f ∈ Δ))
 (v : Option Symbol) (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ vals tmp, TM2.Reaches machine
 (cfg (.wkCheck (.copy (.scan (.run 2 .start)))) v p (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows)
 (cfg (.wkCheck .reject) none p vals [] tmp rows) := by
 obtain ⟨vals,tmp,h⟩ := WeakeningContextCheck.rejects Γ Δ a nsub v (TypedContext.stack s)
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.wkCheck
   WeakeningContextCheck.machine machine agree_wkCheck (storage p [] [] [] rows) h (by simp [config])
 exact ⟨vals,tmp,by simpa [embed_wkCheck,WeakeningContextCheck.args,TypedContext.stack,List.append_assoc] using h⟩

theorem wk_result_run (Δ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.wkResult (.formula0 0)) v p (TypedContext.stack (.formula a :: .context Δ :: s)) [] [] rows)
 (cfg (.wkResult .done) none p (TypedContext.stack s) [] [] (FramedRow.encode (.seq Δ a) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective Control.wkResult
   (FramedRowConstructor.machine false) machine agree_wkResult (storage p [] [] [] [])
   (FramedRowConstructor.construct_seq Δ a v s rows) (by simp [config])
 simpa only [embed_wkResult] using h

theorem wk_drop_run (Γ : ZFR.Context) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.wkDrop (.scan (.run 0 .start))) v p (TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.wkDrop .done) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.context Γ] rfl v vals [] []
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.wkDrop
   TypedBlock.dropMachine machine agree_wkDrop (storage p [] [] [] rows) hw (by simp [config])
 exact ⟨w,by simpa [embed_wkDrop,TypedContext.stack] using h⟩

theorem wk_test_run (Γ Δ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 45 ++ rest) (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows)
 (cfg (.wkCompare .tag) none rest (FramedRow.encode (.seq Γ a) ++ TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 22 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 22)) w rest vals [] [] rows)
   (cfg (.wkCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := wk_copy_run Γ Δ a w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.wkCopy .done) none rest vals [] (TypedContext.stack [.formula a,.context Δ,.context Γ]) rows)
   (cfg (.wkSelect (.save .scan)) none rest vals [] (TypedContext.stack [.formula a,.context Δ,.context Γ]) rows) := global_step rfl
 have hs := wk_select_run Γ Δ a none rest vals rows
 have hsl : TM2.Reaches machine
   (cfg (.wkSelect .done) none rest vals [] (TypedContext.stack [.formula a,.context Γ]) rows)
   (cfg (.wkExpected (.formula0 0)) none rest vals [] (TypedContext.stack [.formula a,.context Γ]) rows) := global_step rfl
 have hx := wk_expected_run Γ a none rest vals rows
 have hxl : TM2.Reaches machine
   (cfg (.wkExpected .done) none rest (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows)
   (cfg (.wkCompare .tag) none rest (FramedRow.encode (.seq Γ a) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hs.trans (hsl.trans (hx.trans hxl))))))

theorem execute_wk (Γ Δ : ZFR.Context) (a : ZFR.Formula) (sub : ∀ f ∈ Γ, f ∈ Δ)
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 45 ++ rest) (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ a) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Δ a) ++ rows)) := by
 let vals := TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)
 let result := FramedRow.encode (.seq Δ a) ++ rows
 have ht := wk_test_run Γ Δ a v rest (FramedRow.encode (.seq Γ a) ++ rows) s
 obtain ⟨w,he⟩ := wk_equal_run (.seq Γ a) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.wkCompare .equal) w rest vals [] [] rows)
   (cfg (.wkCheck (.copy (.scan (.run 2 .start)))) w rest vals [] [] rows) := global_step rfl
 have hc := wk_check_run Γ Δ a sub w rest rows s
 have hcl : TM2.Reaches machine (cfg (.wkCheck .accept) none rest vals [] [] rows)
   (cfg (.wkResult (.formula0 0)) none rest vals [] [] rows) := global_step rfl
 have hr := wk_result_run Δ a none rest rows (.context Γ :: s)
 have hrl : TM2.Reaches machine (cfg (.wkResult .done) none rest (TypedContext.stack (.context Γ :: s)) [] [] result)
   (cfg (.wkDrop (.scan (.run 0 .start))) none rest (TypedContext.stack (.context Γ :: s)) [] [] result) := global_step rfl
 obtain ⟨z,hd⟩ := wk_drop_run Γ none rest (TypedContext.stack s) result
 have hl : TM2.Reaches machine (cfg (.wkDrop .done) z rest (TypedContext.stack s) [] [] result)
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] result) := global_step rfl
 simp only [TM2.Reaches,vals,result,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hc hcl hr hrl hd hl ⊢
 exact ht.trans (he.trans (ha.trans (hc.trans (hcl.trans (hr.trans (hrl.trans (hd.trans hl)))))))

theorem reject_wk_premise (Γ Δ : ZFR.Context) (a : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ a ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 45 ++ rest) (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := wk_test_run Γ Δ a v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := wk_different_run (.seq Γ a) actual hne none rest (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.wkCompare .different) w rest left [] [] right) (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩

theorem reject_wk_subset (Γ Δ : ZFR.Context) (a : ZFR.Formula) (nsub : ¬(∀ f ∈ Γ, f ∈ Δ))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ vals tmp, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 45 ++ rest) (TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ a) ++ rows))
 (cfg .proofReject none rest vals [] tmp rows) := by
 let vals := TypedContext.stack (.formula a :: .context Δ :: .context Γ :: s)
 have ht := wk_test_run Γ Δ a v rest (FramedRow.encode (.seq Γ a) ++ rows) s
 obtain ⟨w,he⟩ := wk_equal_run (.seq Γ a) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.wkCompare .equal) w rest vals [] [] rows)
   (cfg (.wkCheck (.copy (.scan (.run 2 .start)))) w rest vals [] [] rows) := global_step rfl
 obtain ⟨left,tmp,hc⟩ := wk_check_reject Γ Δ a nsub w rest rows s
 have hl : TM2.Reaches machine (cfg (.wkCheck .reject) none rest left [] tmp rows)
   (cfg .proofReject none rest left [] tmp rows) := global_step rfl
 exact ⟨left,tmp,ht.trans (he.trans (ha.trans (hc.trans hl)))⟩
end RosserDirect.ContextProgram
