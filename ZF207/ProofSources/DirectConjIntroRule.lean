module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_ciCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.ciCopy q) = Routine.relocate constructRoles Control.ciCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_ciCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ciCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ciCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ciBuild (q : ConjPremises.Control) (h : (ConjPremises.machine) q ≠ .halt) :
 machine (.ciBuild q) = Routine.relocate moveRoles Control.ciBuild ((ConjPremises.machine) q) := by
 cases q <;> simp_all [machine,ConjPremises.machine]

theorem embed_ciBuild (q : ConjPremises.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.ciBuild (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.ciBuild q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ciCompare (q : RowPairEquality.Control) (h : (RowPairEquality.machine) q ≠ .halt) :
 machine (.ciCompare q) = Routine.relocate rowRoles Control.ciCompare ((RowPairEquality.machine) q) := by
 cases q <;> simp_all [machine,RowPairEquality.machine]

theorem embed_ciCompare (q : RowPairEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles Control.ciCompare (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.ciCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_ciBinary (q : Binary.Control) (h : (Binary.machine 7) q ≠ .halt) :
 machine (.ciBinary q) = Routine.relocate constructRoles Control.ciBinary ((Binary.machine 7) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_ciBinary (q : Binary.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.ciBinary (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.ciBinary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl
theorem ci_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ciCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ciCopy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ciCopy
   TypedBlock.machine machine agree_ciCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_ciCopy,TypedContext.stack,List.append_assoc] using h



theorem ci_build_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.ciBuild (.copy (.scan (.run 2 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
 (cfg (.ciBuild .done) none p (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ TypedContext.stack s) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.ciBuild
   ConjPremises.machine machine agree_ciBuild (storage p [] [] [] rows)
   (ConjPremises.construct Γ a b v [] s) (by simp [config])
 simpa [embed_ciBuild,TypedContext.stack,RowPairEquality.rows,List.append_assoc] using h

theorem ci_equal_run (r t : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.ciCompare (.first .tag)) v p (RowPairEquality.rows r t ++ vals) [] [] (RowPairEquality.rows r t ++ rows))
 (cfg (.ciCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := RowPairEquality.equal_pairs r t v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ciCompare
   RowPairEquality.machine machine agree_ciCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,by simpa only [embed_ciCompare] using h⟩

theorem ci_different_run (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.ciCompare (.first .tag)) v p (RowPairEquality.rows r₁ r₂ ++ vals) [] [] (RowPairEquality.rows t₁ t₂ ++ rows))
 (cfg (.ciCompare .different) w p left [] [] right) := by
 obtain ⟨w,left,right,hw⟩ := RowPairEquality.different_pairs r₁ r₂ t₁ t₂ hne v vals [] rows
 have h := Routine.lift_embedded_run rowRoles row_injective Control.ciCompare
   RowPairEquality.machine machine agree_ciCompare (storage p [] [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa only [embed_ciCompare] using h⟩

theorem ci_binary_run (a b : ZFR.Formula) (v : Option Symbol) (p src rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.ciBinary .boot) v p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ src) [] [] rows)
 (cfg (.ciBinary .done) none p src [] (TypedContext.value (.formula (.and a b))) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.ciBinary
   (Binary.machine 7) machine agree_ciBinary (storage p [] [] [] rows)
   (binary_local 0 a b v src []) (by simp [config])
 simpa [embed_ciBinary,binaryFormula] using h

theorem ci_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 31 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.ciCompare (.first .tag)) none rest (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 15 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 15)) w rest vals [] [] rows)
   (cfg (.ciCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ci_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.ciCopy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.ciBuild (.copy (.scan (.run 2 .start)))) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ci_build_run Γ a b none rest rows (.formula b :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.ciBuild .done) none rest (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ vals) [] [] rows)
   (cfg (.ciCompare (.first .tag)) none rest (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ vals) [] [] rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))

theorem execute_ci (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 31 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.and a b)) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.context Γ :: s)
 have ht := ci_test_run Γ a b v rest (RowPairEquality.rows (.seq Γ b) (.seq Γ a) ++ rows) s
 obtain ⟨w,he⟩ := ci_equal_run (.seq Γ b) (.seq Γ a) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.ciCompare .equal) w rest vals [] [] rows)
   (cfg (.ciBinary .boot) w rest vals [] [] rows) := global_step rfl
 have hb := ci_binary_run a b w rest suffix rows
 have hbl : TM2.Reaches machine
   (cfg (.ciBinary .done) none rest suffix [] (TypedContext.value (.formula (.and a b))) rows)
   (cfg (.diMove .scan) none rest suffix [] (TypedContext.value (.formula (.and a b))) rows) := global_step rfl
 have hm := di_move_run (.and a b) none rest suffix rows
 have hml : TM2.Reaches machine
   (cfg (.diMove .done) none rest (TypedContext.value (.formula (.and a b)) ++ suffix) [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest (TypedContext.value (.formula (.and a b)) ++ suffix) [] [] rows) := global_step rfl
 have hr := di_result_run Γ (.and a b) none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.and a b)) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.and a b)) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hb hbl hm hml hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hb.trans (hbl.trans (hm.trans (hml.trans (hr.trans hl)))))))


theorem reject_ci (Γ : ZFR.Context) (a b : ZFR.Formula) (actual₁ actual₂ : ZFR.Row)
 (hne : ¬(ZFR.Row.seq Γ b = actual₁ ∧ ZFR.Row.seq Γ a = actual₂))
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 31 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (RowPairEquality.rows actual₁ actual₂ ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := ci_test_run Γ a b v rest (RowPairEquality.rows actual₁ actual₂ ++ rows) s
 obtain ⟨w,left,right,he⟩ := ci_different_run (.seq Γ b) (.seq Γ a) actual₁ actual₂ hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.ciCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
