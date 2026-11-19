module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

theorem agree_eeCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.eeCopy q) = Routine.relocate constructRoles Control.eeCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_eeCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.eeCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.eeCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_eeBuild (q : ExistsElimPremises.Q) (h : ExistsElimPremises.machine q ≠ .halt) :
 machine (.eeBuild q) = Routine.relocate quantPremiseRoles Control.eeBuild (ExistsElimPremises.machine q) := by
 cases q <;> simp_all [machine,ExistsElimPremises.machine]

theorem embed_eeBuild (q : ExistsElimPremises.Q) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 FourStack.embed4 quantPremiseRoles Control.eeBuild (FourStack.cfg4 q v p tmp scr vals) (fun _ => rows) =
 cfg (.eeBuild q) v p vals scr tmp rows := by
 unfold FourStack.embed4 cfg FourStack.cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_eeCompare (q : RowPairEquality.Control) (h : (RowPairEquality.machine) q ≠ .halt) :
 machine (.eeCompare q) = Routine.relocate rowRoles Control.eeCompare ((RowPairEquality.machine) q) := by
 cases q <;> simp_all [machine,RowPairEquality.machine]

theorem embed_eeCompare (q : RowPairEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.eeCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.eeCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ee_copy_run (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.eeCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.eeCopy .done) none p (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula c,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.eeCopy
   TypedBlock.machine machine agree_eeCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula c,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_eeCopy,TypedContext.stack,List.append_assoc] using h




theorem ee_build_run (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.eeBuild (.copy (.scan (.run 2 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula c,.formula a,.context Γ]) rows)
 (cfg (.eeBuild .done) none p (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ TypedContext.stack s) [] [] rows) := by
 have h := FourStack.lift4_run quantPremiseRoles quantPremise_injective Control.eeBuild
   ExistsElimPremises.machine machine agree_eeBuild (fun _ => rows)
   (ExistsElimPremises.construct Γ a c v p [] (TypedContext.stack s)) (by simp [FourStack.cfg4])
 simpa [embed_eeBuild,TypedContext.stack,RowPairEquality.rows,List.append_assoc] using h

theorem ee_equal_run (r t : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.eeCompare (.first .tag)) v p (RowPairEquality.rows r t ++ vals) [] [] (RowPairEquality.rows r t ++ rows))
 (cfg (.eeCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := RowPairEquality.equal_pairs r t v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.eeCompare
   RowPairEquality.machine machine agree_eeCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_eeCompare] using h⟩

theorem ee_different_run (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.eeCompare (.first .tag)) v p (RowPairEquality.rows r₁ r₂ ++ vals) [] [] (RowPairEquality.rows t₁ t₂ ++ rows))
 (cfg (.eeCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := RowPairEquality.different_pairs r₁ r₂ t₁ t₂ hne v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.eeCompare
   RowPairEquality.machine machine agree_eeCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_eeCompare] using h⟩


theorem agree_eeResult (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.eeResult q) = Routine.relocate rowRoles Control.eeResult (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_eeResult (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.eeResult (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.eeResult q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_eeSelect (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.eeSelect q) = Routine.relocate constructRoles Control.eeSelect (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_eeSelect (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.eeSelect (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.eeSelect q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ee_result_run (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.eeSelect (.save .scan)) v p (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.eeResult .done) none p (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows)) := by
 have h0 := Routine.lift_embedded_run constructRoles construct_injective Control.eeSelect
   SelectSecond.machine machine agree_eeSelect (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) c v (TypedContext.value (.context Γ) ++ TypedContext.stack s) []) (by simp [config])
 simp only [embed_eeSelect] at h0
 have h1 : TM2.Reaches machine
   (cfg (.eeSelect .done) none p (TypedContext.value (.formula c) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s) [] [] rows)
   (cfg (.eeResult (.formula0 0)) none p (TypedContext.value (.formula c) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s) [] [] rows) := global_step rfl
 have h2 := Routine.lift_embedded_run rowRoles row_injective Control.eeResult
   (FramedRowConstructor.machine false) machine agree_eeResult (storage p [] [] [] [])
   (FramedRowConstructor.construct_seq_raw Γ c none (TypedContext.stack s) rows) (by simp [config])
 simp only [embed_eeResult] at h2
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at h0 h1 h2 ⊢
 exact h0.trans (h1.trans h2)

theorem ee_test_run (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 53 ++ rest) (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.eeCompare (.first .tag)) none rest (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 26 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 26)) w rest vals [] [] rows)
   (cfg (.eeCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ee_copy_run Γ a c w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.eeCopy .done) none rest vals [] (TypedContext.stack [.formula c,.formula a,.context Γ]) rows)
   (cfg (.eeBuild (.copy (.scan (.run 2 .start)))) none rest vals [] (TypedContext.stack [.formula c,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ee_build_run Γ a c none rest rows (.formula c :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.eeBuild .done) none rest (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ vals) [] [] rows)
   (cfg (.eeCompare (.first .tag)) none rest (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))


theorem execute_exE (Γ : ZFR.Context) (a c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 53 ++ rest) (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows)) := by
 let vals := TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)
 have ht := ee_test_run Γ a c v rest (RowPairEquality.rows (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) ++ rows) s
 obtain ⟨w,he⟩ := ee_equal_run (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.eeCompare .equal) w rest vals [] [] rows)
   (cfg (.eeSelect (.save .scan)) w rest vals [] [] rows) := global_step rfl
 have hr := ee_result_run Γ a c w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.eeResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows)) := global_step rfl
 exact ht.trans (he.trans (ha.trans (hr.trans hl)))

theorem reject_exE (Γ : ZFR.Context) (a c : ZFR.Formula) (actual₁ actual₂ : ZFR.Row)
 (hne : ¬(ZFR.Row.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c) = actual₁ ∧ ZFR.Row.seq Γ (.ex a) = actual₂))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 53 ++ rest) (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows actual₁ actual₂ ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := ee_test_run Γ a c v rest (RowPairEquality.rows actual₁ actual₂ ++ rows) s
 obtain ⟨w,left,right,he⟩ := ee_different_run (.seq (a :: ZFR.shiftContext Γ) (ZFR.shift c)) (.seq Γ (.ex a)) actual₁ actual₂ hne none rest (TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.eeCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
