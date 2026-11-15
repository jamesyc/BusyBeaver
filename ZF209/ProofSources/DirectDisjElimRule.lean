module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_deCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.deCopy q) = Routine.relocate constructRoles Control.deCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_deCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.deCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.deCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_deBuild (q : DisjElimPremises.Control) (h : (DisjElimPremises.machine) q ≠ .halt) :
 machine (.deBuild q) = Routine.relocate moveRoles Control.deBuild ((DisjElimPremises.machine) q) := by
 cases q <;> simp_all [machine,DisjElimPremises.machine]

theorem embed_deBuild (q : DisjElimPremises.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.deBuild (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.deBuild q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_deCompare (q : RowPairEquality.Control) (h : (RowPairEquality.machine) q ≠ .halt) :
 machine (.deCompare q) = Routine.relocate rowRoles Control.deCompare ((RowPairEquality.machine) q) := by
 cases q <;> simp_all [machine,RowPairEquality.machine]

theorem embed_deCompare (q : RowPairEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.deCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.deCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem de_copy_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.deCopy (.scan (.run 3 .start))) v p (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.deCopy .done) none p (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.deCopy
   TypedBlock.machine machine agree_deCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 3 [.formula c,.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_deCopy,TypedContext.stack,List.append_assoc] using h




theorem de_build_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.deBuild (.copy (.scan (.run 3 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows)
 (cfg (.deBuild .done) none p (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ TypedContext.stack s) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.deBuild
   DisjElimPremises.machine machine agree_deBuild (storage p [] [] [] rows)
   (DisjElimPremises.construct Γ a b c v [] s) (by simp [config])
 simpa [embed_deBuild,TypedContext.stack,DisjElimPremises.field,DisjElimPremises.context,RowPairEquality.rows,List.append_assoc] using h
theorem de_equal_run (r t : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.deCompare (.first .tag)) v p (RowPairEquality.rows r t ++ vals) [] [] (RowPairEquality.rows r t ++ rows))
 (cfg (.deCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := RowPairEquality.equal_pairs r t v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.deCompare
   RowPairEquality.machine machine agree_deCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_deCompare] using h⟩

theorem de_different_run (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.deCompare (.first .tag)) v p (RowPairEquality.rows r₁ r₂ ++ vals) [] [] (RowPairEquality.rows t₁ t₂ ++ rows))
 (cfg (.deCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := RowPairEquality.different_pairs r₁ r₂ t₁ t₂ hne v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.deCompare
   RowPairEquality.machine machine agree_deCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_deCompare] using h⟩


theorem de_test_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 43 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.deCompare (.first .tag)) none rest (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 21 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 21)) w rest vals [] [] rows)
   (cfg (.deCopy (.scan (.run 3 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := de_copy_run Γ a b c w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.deCopy .done) none rest vals [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows)
   (cfg (.deBuild (.copy (.scan (.run 3 .start)))) none rest vals [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := de_build_run Γ a b c none rest rows (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.deBuild .done) none rest (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ vals) [] [] rows)
   (cfg (.deCompare (.first .tag)) none rest (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))



theorem agree_deSelectB (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.deSelectB q) = Routine.relocate constructRoles Control.deSelectB (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_deSelectB (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.deSelectB (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.deSelectB q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem deSelectB_run (a c : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.deSelectB (.save .scan)) v p (TypedContext.value (.formula c) ++ TypedContext.value (.formula a) ++ vals) [] [] rows)
 (cfg (.deSelectB .done) none p (TypedContext.value (.formula c) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.deSelectB
   SelectSecond.machine machine agree_deSelectB (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) c v vals []) (by simp [config])
 simpa only [embed_deSelectB] using h

theorem agree_deSelectA (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.deSelectA q) = Routine.relocate constructRoles Control.deSelectA (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_deSelectA (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.deSelectA (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.deSelectA q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem deSelectA_run (a c : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.deSelectA (.save .scan)) v p (TypedContext.value (.formula c) ++ TypedContext.value (.formula a) ++ vals) [] [] rows)
 (cfg (.deSelectA .done) none p (TypedContext.value (.formula c) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.deSelectA
   SelectSecond.machine machine agree_deSelectA (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) c v vals []) (by simp [config])
 simpa only [embed_deSelectA] using h

theorem execute_de (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 43 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows)) := by
 let vals := TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 let mid := TypedContext.stack (.formula c :: .formula a :: .context Γ :: s)
 let tail := TypedContext.stack (.formula c :: .context Γ :: s)
 have ht := de_test_run Γ a b c v rest (RowPairEquality.rows (.branches Γ a b c) (.seq Γ (.or a b)) ++ rows) s
 obtain ⟨w,he⟩ := de_equal_run (.branches Γ a b c) (.seq Γ (.or a b)) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.deCompare .equal) w rest vals [] [] rows)
   (cfg (.deSelectB (.save .scan)) w rest vals [] [] rows) := global_step rfl
 have hb := deSelectB_run b c w rest (TypedContext.stack (.formula a :: .context Γ :: s)) rows
 have hbl : TM2.Reaches machine (cfg (.deSelectB .done) none rest mid [] [] rows)
   (cfg (.deSelectA (.save .scan)) none rest mid [] [] rows) := global_step rfl
 have hc := deSelectA_run a c none rest (TypedContext.stack (.context Γ :: s)) rows
 have hcl : TM2.Reaches machine (cfg (.deSelectA .done) none rest tail [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest tail [] [] rows) := global_step rfl
 have hr := di_result_run Γ c none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ c) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,mid,tail,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hb hbl hc hcl hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hb.trans (hbl.trans (hc.trans (hcl.trans (hr.trans hl)))))))
theorem reject_de (Γ : ZFR.Context) (a b c : ZFR.Formula) (actual₁ actual₂ : ZFR.Row)
 (hne : ¬(ZFR.Row.branches Γ a b c = actual₁ ∧ ZFR.Row.seq Γ (.or a b) = actual₂))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 43 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows actual₁ actual₂ ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := de_test_run Γ a b c v rest (RowPairEquality.rows actual₁ actual₂ ++ rows) s
 obtain ⟨w,left,right,he⟩ := de_different_run (.branches Γ a b c) (.seq Γ (.or a b)) actual₁ actual₂ hne none rest (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.deCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
