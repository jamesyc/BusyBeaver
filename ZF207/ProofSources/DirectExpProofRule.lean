module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing
set_option backward.isDefEq.respectTransparency false

theorem enter_exp (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode 14)) v p vals [] [] rows) =
 some (cfg (.expCopy (.scan (.run 1 .start))) v p vals [] [] rows) := rfl

theorem leave_expCopy (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg (.expCopy .done) v p vals [] tmp rows) =
 some (cfg .expDrop v p vals [] tmp rows) := rfl

theorem exp_drop_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
 (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .expDrop v p vals [] (x :: tmp) rows) =
 some (cfg .expDrop (some x) p vals [] tmp rows) := by
 cases x <;> simp_all [machine,cfg,TM2.step,TM2.stepAux,storage]
 all_goals funext k; cases k <;> rfl

theorem exp_drop_end (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .expDrop v p vals [] (.frameEnd :: tmp) rows) =
 some (cfg .expBottom (some .frameEnd) p vals [] tmp rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem exp_drop_frame (payload : List Symbol) (valid : ∀ x ∈ payload, x ≠ .frameEnd)
 (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine (cfg .expDrop v p vals [] (payload ++ .frameEnd :: tmp) rows)
 (cfg .expBottom (some .frameEnd) p vals [] tmp rows) := by
 induction payload generalizing v with
 | nil => exact global_step (exp_drop_end v p vals tmp rows)
 | cons x xs ih =>
   exact (global_step (exp_drop_step x (valid x (by simp)) v p vals (xs ++ .frameEnd :: tmp) rows)).trans
     (ih (by intro y hy; exact valid y (by simp [hy])) (some x))

theorem exp_bottom_step (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .expBottom v p vals [] tmp rows) =
 some (cfg (.expExpected (.formula0 0)) v p vals [] (TypedContext.value (.formula .bot) ++ tmp) rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage,TypedContext.value,valueSymbols,valueTokens,payloadBits,tokenBits]
 funext k; cases k <;> rfl

theorem leave_expExpected (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.expExpected .done) v p vals [] [] rows) =
 some (cfg (.expCompare .tag) v p vals [] [] rows) := rfl

theorem accept_expCompare (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.expCompare .equal) v p vals [] [] rows) =
 some (cfg (.expResult (.formula0 0)) v p vals [] [] rows) := rfl

theorem reject_expCompare (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.expCompare .different) v p vals [] [] rows) =
 some (cfg .proofReject v p vals [] [] rows) := rfl

theorem leave_expResult (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.expResult .done) v p vals [] [] rows) =
 some (cfg (.dispatch .start) v p vals [] [] rows) := rfl

theorem exp_test_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 29 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
 (cfg (.expCompare .tag) none rest
   (FramedRow.encode (.seq Γ .bot) ++ TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows) := by
 let vals := TypedContext.stack (.formula f :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 14 v rest vals [] [] rows
 have he := global_step (enter_exp w rest vals rows)
 have hc := exp_copy_run Γ f w rest rows s
 have hl := global_step (leave_expCopy none rest vals (TypedContext.stack [.formula f,.context Γ]) rows)
 have hdrop := exp_drop_frame (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) none rest vals (TypedContext.value (.context Γ)) rows
 have hb := global_step (exp_bottom_step (some .frameEnd) rest vals (TypedContext.value (.context Γ)) rows)
 have hx := exp_expected_run Γ (some .frameEnd) rest vals rows
 have hy := global_step (leave_expExpected none rest (FramedRow.encode (.seq Γ .bot) ++ vals) rows)
 simp only [TM2.Reaches,vals,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   TypedContext.value,valueSymbols,List.append_assoc,List.singleton_append] at hd he hc hl hdrop hb hx hy ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hdrop.trans (hb.trans (hx.trans hy))))))

/-- Actual explosion inference: consume exactly the checked premise Γ ⊢ ⊥,
produce Γ ⊢ f, and preserve arbitrary program/value/row suffixes. -/
theorem execute_exp (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 29 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] (FramedRow.encode (.seq Γ .bot) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := by
 have ht := exp_test_run Γ f v rest (FramedRow.encode (.seq Γ .bot) ++ rows) s
 obtain ⟨w,he⟩ := exp_equal_run (.seq Γ .bot) none rest (TypedContext.stack (.formula f :: .context Γ :: s)) rows
 have ha := global_step (accept_expCompare w rest (TypedContext.stack (.formula f :: .context Γ :: s)) rows)
 have hr := exp_result_run Γ f w rest rows s
 have hl := global_step (leave_expResult none rest (TypedContext.stack s) (FramedRow.encode (.seq Γ f) ++ rows))
 exact ht.trans (he.trans (ha.trans (hr.trans hl)))

theorem reject_exp (Γ : ZFR.Context) (f : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq Γ .bot ≠ actual) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 29 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 have ht := exp_test_run Γ f v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := exp_different_run (.seq Γ .bot) actual hne none rest (TypedContext.stack (.formula f :: .context Γ :: s)) rows
 exact ⟨w,left,right,ht.trans (he.trans (global_step (reject_expCompare w rest left right)))⟩

end RosserDirect.ContextProgram
