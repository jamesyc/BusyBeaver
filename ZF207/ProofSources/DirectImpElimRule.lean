module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_ieCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.ieCopy q) = Routine.relocate constructRoles Control.ieCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_ieCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ieCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ieCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ieBuild (q : ImpElimPremises.Control) (h : (ImpElimPremises.machine) q ≠ .halt) :
 machine (.ieBuild q) = Routine.relocate moveRoles Control.ieBuild ((ImpElimPremises.machine) q) := by
 cases q <;> simp_all [machine,ImpElimPremises.machine]

theorem embed_ieBuild (q : ImpElimPremises.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ieBuild (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ieBuild q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ieCompare (q : RowPairEquality.Control) (h : (RowPairEquality.machine) q ≠ .halt) :
 machine (.ieCompare q) = Routine.relocate rowRoles Control.ieCompare ((RowPairEquality.machine) q) := by
 cases q <;> simp_all [machine,RowPairEquality.machine]

theorem embed_ieCompare (q : RowPairEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.ieCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.ieCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ie_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ieCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ieCopy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ieCopy
   TypedBlock.machine machine agree_ieCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_ieCopy,TypedContext.stack,List.append_assoc] using h



theorem ie_build_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ieBuild (.copy (.scan (.run 1 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
 (cfg (.ieBuild .done) none p (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ TypedContext.stack s) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ieBuild
   ImpElimPremises.machine machine agree_ieBuild (storage p [] [] [] rows)
   (ImpElimPremises.construct Γ a b v [] s) (by simp [config])
 simpa [embed_ieBuild,TypedContext.stack,RowPairEquality.rows,List.append_assoc] using h

theorem ie_equal_run (r t : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.ieCompare (.first .tag)) v p (RowPairEquality.rows r t ++ vals) [] [] (RowPairEquality.rows r t ++ rows))
 (cfg (.ieCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := RowPairEquality.equal_pairs r t v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ieCompare
   RowPairEquality.machine machine agree_ieCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_ieCompare] using h⟩

theorem ie_different_run (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.ieCompare (.first .tag)) v p (RowPairEquality.rows r₁ r₂ ++ vals) [] [] (RowPairEquality.rows t₁ t₂ ++ rows))
 (cfg (.ieCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := RowPairEquality.different_pairs r₁ r₂ t₁ t₂ hne v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ieCompare
   RowPairEquality.machine machine agree_ieCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_ieCompare] using h⟩

theorem agree_ieSelect (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.ieSelect q) = Routine.relocate constructRoles Control.ieSelect (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_ieSelect (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ieSelect (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ieSelect q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ie_select_run (a b : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ieSelect (.save .scan)) v p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ vals) [] [] rows)
 (cfg (.ieSelect .done) none p (TypedContext.value (.formula b) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ieSelect
   SelectSecond.machine machine agree_ieSelect (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) b v vals []) (by simp [config])
 simpa only [embed_ieSelect] using h

theorem ie_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 27 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ieCompare (.first .tag)) none rest (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 13 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 13)) w rest vals [] [] rows)
   (cfg (.ieCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ie_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.ieCopy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.ieBuild (.copy (.scan (.run 1 .start)))) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ie_build_run Γ a b none rest rows (.formula b :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.ieBuild .done) none rest (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ vals) [] [] rows)
   (cfg (.ieCompare (.first .tag)) none rest (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))

theorem execute_ie (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 27 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.formula b :: .context Γ :: s)
 have ht := ie_test_run Γ a b v rest (RowPairEquality.rows (.seq Γ a) (.seq Γ (.imp a b)) ++ rows) s
 obtain ⟨w,he⟩ := ie_equal_run (.seq Γ a) (.seq Γ (.imp a b)) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.ieCompare .equal) w rest vals [] [] rows)
   (cfg (.ieSelect (.save .scan)) w rest vals [] [] rows) := global_step rfl
 have hselect := ie_select_run a b w rest (TypedContext.stack (.context Γ :: s)) rows
 have hsl : TM2.Reaches machine (cfg (.ieSelect .done) none rest suffix [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest suffix [] [] rows) := global_step rfl
 have hr := di_result_run Γ b none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ b) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hselect hsl hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hselect.trans (hsl.trans (hr.trans hl)))))

theorem reject_ie (Γ : ZFR.Context) (a b : ZFR.Formula) (actual₁ actual₂ : ZFR.Row)
 (hne : ¬(ZFR.Row.seq Γ a = actual₁ ∧ ZFR.Row.seq Γ (.imp a b) = actual₂))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 27 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows actual₁ actual₂ ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := ie_test_run Γ a b v rest (RowPairEquality.rows actual₁ actual₂ ++ rows) s
 obtain ⟨w,left,right,he⟩ := ie_different_run (.seq Γ a) (.seq Γ (.imp a b)) actual₁ actual₂ hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.ieCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
