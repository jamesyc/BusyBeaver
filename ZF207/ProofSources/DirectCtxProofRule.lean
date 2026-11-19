module
public import DirectContextProgram
public import DirectSyntaxInterpreter
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing
set_option backward.isDefEq.respectTransparency false

theorem enter_ctx (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode 10)) v p vals [] [] rows) =
 some (cfg (.proofRow (.formula0 0)) v p vals [] [] rows) := rfl

theorem leave_proofRow (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.proofRow .done) v p vals [] [] rows) =
 some (cfg (.proofCopy (.scan .tag)) v p vals [] [] rows) := rfl

theorem leave_proofCopy (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.proofCopy .done) v p vals [] [] rows) =
 some (cfg .proofPopTag v p vals [] [] rows) := rfl

theorem pop_seq_tag (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg .proofPopTag v p (.bit0 :: vals) [] [] rows) =
 some (cfg (.proofPrepare .entry) (some .bit0) p vals [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem leave_proofPrepare (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg (.proofPrepare .done) v p vals [] tmp rows) =
 some (cfg (.proofMember .next) v p vals [] tmp rows) := rfl

theorem accept_member (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg (.proofMember .found) v p vals [] tmp rows) =
 some (cfg .proofDropTarget v p vals [] tmp rows) := rfl

theorem reject_member (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg (.proofMember .absent) v p vals [] tmp rows) =
 some (cfg .proofReject v p vals [] tmp rows) := rfl

theorem drop_target_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
    (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .proofDropTarget v p (x :: vals) [] tmp rows) =
 some (cfg .proofDropTarget (some x) p vals [] tmp rows) := by
 cases x <;> simp_all [machine,cfg,TM2.step,TM2.stepAux,storage]
 all_goals funext k; cases k <;> rfl

theorem drop_target_end (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .proofDropTarget v p (.frameEnd :: vals) [] tmp rows) =
 some (cfg .proofClear (some .frameEnd) p vals [] tmp rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem drop_target (payload : List Symbol) (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine (cfg .proofDropTarget v p (payload ++ .frameEnd :: vals) [] tmp rows)
   (cfg .proofClear (some .frameEnd) p vals [] tmp rows) := by
 induction payload generalizing v with
 | nil => exact global_step (drop_target_end v p vals tmp rows)
 | cons x xs ih =>
   have one := global_step (drop_target_step x (valid x (by simp)) v p (xs ++ .frameEnd :: vals) tmp rows)
   exact one.trans (ih (by intro y hy; exact valid y (by simp [hy])) (some x))

theorem clear_step (x : Symbol) (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.step machine (cfg .proofClear v p vals [] (x :: tmp) rows) =
 some (cfg .proofClear (some x) p vals [] tmp rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem clear_empty (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg .proofClear v p vals [] [] rows) =
 some (cfg (.dispatch .start) none p vals [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage,Function.update]

theorem clear_work (v : Option Symbol) (p vals tmp rows : List Symbol) :
 TM2.Reaches machine (cfg .proofClear v p vals [] tmp rows)
   (cfg (.dispatch .start) none p vals [] [] rows) := by
 induction tmp generalizing v with
 | nil => exact global_step (clear_empty v p vals rows)
 | cons x xs ih => exact (global_step (clear_step x v p vals xs rows)).trans (ih (some x))

theorem ctx_test_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
    (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ tmp, TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 21 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg (.proofMember (if f ∈ Γ then .found else .absent)) none rest
     (FramedRow.formulaFrame f ++ TypedContext.stack s) [] tmp (FramedRow.encode (.seq Γ f) ++ rows)) := by
 let newRows := FramedRow.encode (.seq Γ f) ++ rows
 obtain ⟨w,hd⟩ := dispatch_run 10 v rest (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows
 have he := global_step (enter_ctx w rest (TypedContext.stack (.formula f :: .context Γ :: s)) rows)
 have hc := proof_row_run Γ f w rest rows s
 have hl := global_step (leave_proofRow none rest (TypedContext.stack s) newRows)
 have hcopy := proof_copy_run (.seq Γ f) none rest (TypedContext.stack s) rows
 have hlc := global_step (leave_proofCopy none rest (FramedRow.encode (.seq Γ f) ++ TypedContext.stack s) newRows)
 have hp := global_step (pop_seq_tag none rest (FramedContext.encode Γ ++ FramedRow.formulaFrame f ++ TypedContext.stack s) newRows)
 have hprep := proof_prepare_run Γ (some .bit0) rest (FramedRow.formulaFrame f ++ TypedContext.stack s) newRows
 have hpleave := global_step (leave_proofPrepare none rest (FramedRow.formulaFrame f ++ TypedContext.stack s) (Membership.contextFrames Γ) newRows)
 obtain ⟨tmp,hm⟩ := proof_membership_run Γ f none rest (TypedContext.stack s) newRows
 simp only [TM2.Reaches,newRows,FramedRow.encode,List.cons_append,List.append_assoc] at hd he hc hl hcopy hlc hp hprep hpleave hm ⊢
 refine ⟨tmp,?_⟩
 exact hd.trans <| he.trans <| hc.trans <| hl.trans <| hcopy.trans <| hlc.trans <| hp.trans <| hprep.trans <| hpleave.trans hm

/-- Actual checked ctx inference, not just construction of certificate data.
Only successful membership reaches the accepted-row continuation. -/
theorem execute_ctx (Γ : ZFR.Context) (f : ZFR.Formula) (member : f ∈ Γ)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 21 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := by
 obtain ⟨tmp,ht⟩ := ctx_test_run Γ f v rest rows s
 simp only [member,↓reduceIte] at ht
 have ha := global_step (accept_member none rest (FramedRow.formulaFrame f ++ TypedContext.stack s) tmp (FramedRow.encode (.seq Γ f) ++ rows))
 have hd := drop_target (Membership.formulaPayload f) (payloadBits_no_end _) none rest (TypedContext.stack s) tmp (FramedRow.encode (.seq Γ f) ++ rows)
 have hc := clear_work (some .frameEnd) rest (TypedContext.stack s) tmp (FramedRow.encode (.seq Γ f) ++ rows)
 simp only [TM2.Reaches,FramedRow.formulaFrame,List.append_assoc,List.singleton_append] at ht ha hd hc ⊢
 exact ht.trans (ha.trans (hd.trans hc))

/-- Invalid ctx membership reaches the explicit rejecting control state.
The provisional row is never committed by returning to dispatch. -/
theorem reject_ctx (Γ : ZFR.Context) (f : ZFR.Formula) (notMember : f ∉ Γ)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ tmp, TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 21 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
   (cfg .proofReject none rest (FramedRow.formulaFrame f ++ TypedContext.stack s) [] tmp (FramedRow.encode (.seq Γ f) ++ rows)) := by
 obtain ⟨tmp,ht⟩ := ctx_test_run Γ f v rest rows s
 simp only [notMember,↓reduceIte] at ht
 exact ⟨tmp,ht.trans (global_step (reject_member none rest (FramedRow.formulaFrame f ++ TypedContext.stack s) tmp (FramedRow.encode (.seq Γ f) ++ rows)))⟩



/-- Complete canonical ctx certificate program, including parsing its arbitrary
context/formula fields, validates into the exact source-calculus sequent. -/
theorem execute_ctx_program (Γ : ZFR.Context) (f : ZFR.Formula) (member : f ∈ Γ)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (payloadBits (ZFR.TokenVM.emitCert (.ctx Γ f)) ++ rest) (TypedContext.stack s) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := by
 have hg := SyntaxInterpreter.context_runs Γ s v (payloadBits (ZFR.TokenVM.emitFormula f) ++ tokenBits 21 ++ rest) rows
 have hf := SyntaxInterpreter.formula_runs f (.context Γ :: s) none (tokenBits 21 ++ rest) rows
 have hc := execute_ctx Γ f member none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg hf hc
 simpa [TM2.Reaches,ZFR.TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using hg.trans (hf.trans hc)

theorem reject_ctx_program (Γ : ZFR.Context) (f : ZFR.Formula) (notMember : f ∉ Γ)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ tmp, TM2.Reaches machine
   (cfg (.dispatch .start) v (payloadBits (ZFR.TokenVM.emitCert (.ctx Γ f)) ++ rest) (TypedContext.stack s) [] [] rows)
   (cfg .proofReject none rest (FramedRow.formulaFrame f ++ TypedContext.stack s) [] tmp (FramedRow.encode (.seq Γ f) ++ rows)) := by
 have hg := SyntaxInterpreter.context_runs Γ s v (payloadBits (ZFR.TokenVM.emitFormula f) ++ tokenBits 21 ++ rest) rows
 have hf := SyntaxInterpreter.formula_runs f (.context Γ :: s) none (tokenBits 21 ++ rest) rows
 obtain ⟨tmp,hc⟩ := reject_ctx Γ f notMember none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg hf hc
 refine ⟨tmp,?_⟩
 simpa [TM2.Reaches,ZFR.TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using hg.trans (hf.trans hc)

end RosserDirect.ContextProgram
