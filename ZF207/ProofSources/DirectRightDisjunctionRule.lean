module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
theorem agree_di2Copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.di2Copy q) = Routine.relocate constructRoles Control.di2Copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_di2Copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.di2Copy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.di2Copy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem di2_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.di2Copy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.di2Copy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.di2Copy
   TypedBlock.machine machine agree_di2Copy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_di2Copy,TypedContext.stack,List.append_assoc] using h


theorem agree_di2Select (q : SelectSecond.Control) (h : SelectSecond.machine q ≠ .halt) :
 machine (.di2Select q) = Routine.relocate moveRoles Control.di2Select (SelectSecond.machine q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_di2Select (q : SelectSecond.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.di2Select (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.di2Select q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem di2_select_run (a b : ZFR.Formula) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.di2Select (.save .scan)) v p vals [] (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ tmp) rows)
 (cfg (.di2Select .done) none p vals [] (TypedContext.value (.formula b) ++ tmp) rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.di2Select
   SelectSecond.machine machine agree_di2Select (storage p [] [] [] rows)
   (SelectSecond.select_second (.formula a) b v tmp vals) (by simp [config])
 simpa only [embed_di2Select] using h

theorem di2_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 39 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.diCompare .tag) none rest (FramedRow.encode (.seq Γ b) ++ TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 19 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 19)) w rest vals [] [] rows)
   (cfg (.di2Copy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := di2_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.di2Copy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.di2Select (.save .scan)) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have ht := di2_select_run a b none rest vals (TypedContext.value (.context Γ)) rows
 have htl : TM2.Reaches machine
   (cfg (.di2Select .done) none rest vals [] (TypedContext.stack [.formula b,.context Γ]) rows)
   (cfg (.diExpected (.formula0 0)) none rest vals [] (TypedContext.stack [.formula b,.context Γ]) rows) := global_step rfl
 have hx := di_expected_run Γ b none rest vals rows
 have hy : TM2.Reaches machine
   (cfg (.diExpected .done) none rest (FramedRow.encode (.seq Γ b) ++ vals) [] [] rows)
   (cfg (.diCompare .tag) none rest (FramedRow.encode (.seq Γ b) ++ vals) [] [] rows) := global_step rfl
 simp only [TM2.Reaches,vals,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hl ht htl hx hy ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (ht.trans (htl.trans (hx.trans hy))))))
theorem execute_di2 (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 39 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ b) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.or a b)) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.context Γ :: s)
 have ht := di2_test_run Γ a b v rest (FramedRow.encode (.seq Γ b) ++ rows) s
 obtain ⟨w,he⟩ := di_equal_run (.seq Γ b) none rest vals rows
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

theorem reject_di2 (Γ : ZFR.Context) (a b : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ b ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 39 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := di2_test_run Γ a b v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := di_different_run (.seq Γ b) actual hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.diCompare .different) w rest left [] [] right)
   (cfg .proofReject w rest left [] [] right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
