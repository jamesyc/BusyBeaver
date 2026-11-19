module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_bpCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.bpCopy q) = Routine.relocate constructRoles Control.bpCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_bpCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.bpCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.bpCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_bpBuild (q : BranchPremises.Control) (h : (BranchPremises.machine) q ≠ .halt) :
 machine (.bpBuild q) = Routine.relocate moveRoles Control.bpBuild ((BranchPremises.machine) q) := by
 cases q <;> simp_all [machine,BranchPremises.machine]

theorem embed_bpBuild (q : BranchPremises.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.bpBuild (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.bpBuild q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_bpCompare (q : RowPairEquality.Control) (h : (RowPairEquality.machine) q ≠ .halt) :
 machine (.bpCompare q) = Routine.relocate rowRoles Control.bpCompare ((RowPairEquality.machine) q) := by
 cases q <;> simp_all [machine,RowPairEquality.machine]

theorem embed_bpCompare (q : RowPairEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.bpCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.bpCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem bp_copy_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.bpCopy (.scan (.run 3 .start))) v p (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.bpCopy .done) none p (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.bpCopy
   TypedBlock.machine machine agree_bpCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 3 [.formula c,.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_bpCopy,TypedContext.stack,List.append_assoc] using h




theorem bp_build_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.bpBuild (.copy (.scan (.run 3 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows)
 (cfg (.bpBuild .done) none p (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ TypedContext.stack s) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.bpBuild
   BranchPremises.machine machine agree_bpBuild (storage p [] [] [] rows)
   (BranchPremises.construct Γ a b c v [] (TypedContext.stack s)) (by simp [config])
 simpa [embed_bpBuild,TypedContext.stack,BranchPremises.field,BranchPremises.context,RowPairEquality.rows,List.append_assoc] using h
theorem bp_equal_run (r t : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.bpCompare (.first .tag)) v p (RowPairEquality.rows r t ++ vals) [] [] (RowPairEquality.rows r t ++ rows))
 (cfg (.bpCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := RowPairEquality.equal_pairs r t v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.bpCompare
   RowPairEquality.machine machine agree_bpCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_bpCompare] using h⟩

theorem bp_different_run (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.bpCompare (.first .tag)) v p (RowPairEquality.rows r₁ r₂ ++ vals) [] [] (RowPairEquality.rows t₁ t₂ ++ rows))
 (cfg (.bpCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := RowPairEquality.different_pairs r₁ r₂ t₁ t₂ hne v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.bpCompare
   RowPairEquality.machine machine agree_bpCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_bpCompare] using h⟩


theorem agree_bpResult (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine true q ≠ .halt) :
 machine (.bpResult q) = Routine.relocate rowRoles Control.bpResult (FramedRowConstructor.machine true q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_bpResult (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.bpResult (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.bpResult q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem bp_result_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.bpResult (.formula0 2)) v p (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.bpResult .done) none p (TypedContext.stack s) [] [] (FramedRow.encode (.branches Γ a b c) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective Control.bpResult
   (FramedRowConstructor.machine true) machine agree_bpResult (storage p [] [] [] [])
   (FramedRowConstructor.construct_branches Γ a b c v s rows) (by simp [config])
 simpa only [embed_bpResult] using h
theorem bp_test_run (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 41 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.bpCompare (.first .tag)) none rest (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 20 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 20)) w rest vals [] [] rows)
   (cfg (.bpCopy (.scan (.run 3 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := bp_copy_run Γ a b c w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.bpCopy .done) none rest vals [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows)
   (cfg (.bpBuild (.copy (.scan (.run 3 .start)))) none rest vals [] (TypedContext.stack [.formula c,.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := bp_build_run Γ a b c none rest rows (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.bpBuild .done) none rest (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ vals) [] [] rows)
   (cfg (.bpCompare (.first .tag)) none rest (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))


theorem execute_branchPair (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 41 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.branches Γ a b c) ++ rows)) := by
 let vals := TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)
 have ht := bp_test_run Γ a b c v rest (RowPairEquality.rows (.seq (b :: Γ) c) (.seq (a :: Γ) c) ++ rows) s
 obtain ⟨w,he⟩ := bp_equal_run (.seq (b :: Γ) c) (.seq (a :: Γ) c) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.bpCompare .equal) w rest vals [] [] rows)
   (cfg (.bpResult (.formula0 2)) w rest vals [] [] rows) := global_step rfl
 have hr := bp_result_run Γ a b c w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.bpResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.branches Γ a b c) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.branches Γ a b c) ++ rows)) := global_step rfl
 exact ht.trans (he.trans (ha.trans (hr.trans hl)))

theorem reject_branchPair (Γ : ZFR.Context) (a b c : ZFR.Formula) (actual₁ actual₂ : ZFR.Row)
 (hne : ¬(ZFR.Row.seq (b :: Γ) c = actual₁ ∧ ZFR.Row.seq (a :: Γ) c = actual₂))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 41 ++ rest) (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows actual₁ actual₂ ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := bp_test_run Γ a b c v rest (RowPairEquality.rows actual₁ actual₂ ++ rows) s
 obtain ⟨w,left,right,he⟩ := bp_different_run (.seq (b :: Γ) c) (.seq (a :: Γ) c) actual₁ actual₂ hne none rest (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.bpCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
