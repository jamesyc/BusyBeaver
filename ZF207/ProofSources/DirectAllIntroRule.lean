module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem agree_aiCopy (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.aiCopy q) = Routine.relocate constructRoles Control.aiCopy (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem embed_aiCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.aiCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.aiCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_aiCompare (q : FramedRowEquality.Control) (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.aiCompare q) = Routine.relocate rowRoles Control.aiCompare (FramedRowEquality.machine q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]
theorem embed_aiCompare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr rows : List Symbol) :
 Routine.embed rowRoles Control.aiCompare (config q v vals scr rows) (storage p [] [] [] []) =
 cfg (.aiCompare q) v p vals scr [] rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_aiResult (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.aiResult q) = Routine.relocate rowRoles Control.aiResult ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]
theorem embed_aiResult (q : FramedRowConstructor.Control) (v : Option Symbol) (p vals scr rows : List Symbol) :
 Routine.embed rowRoles Control.aiResult (config q v vals scr rows) (storage p [] [] [] []) =
 cfg (.aiResult q) v p vals scr [] rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl
theorem agree_aiUnary (q : RosserDirect.Label)
    (h : RosserDirect.Append.machine (tokenBits (13)) q ≠ .halt) :
 machine (.aiUnary q) = Routine.relocate constructRoles Control.aiUnary
   (RosserDirect.Append.machine (tokenBits (13)) q) := by
 cases q <;> simp_all [machine,RosserDirect.Append.machine]

theorem agree_aiMove (q : RosserDirect.Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.aiMove q) = Routine.relocate moveRoles Control.aiMove (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_aiUnary (q : RosserDirect.Label) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.aiUnary (RosserDirect.cfg q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.aiUnary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_aiMove (q : RosserDirect.Label) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.aiMove (RosserDirect.cfg q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.aiMove q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ai_unary_run (f : ZFR.Formula) (v : Option Symbol)
    (program src rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.aiUnary .scan) v program (Membership.formulaPayload f ++ .frameEnd :: src) [] [] rows)
   (cfg (.aiUnary .done) none program src []
     (Membership.formulaPayload (.all f) ++ [.frameEnd]) rows) := by
 have localRun := RosserDirect.Append.append_frame (tokenBits (13))
   (Membership.formulaPayload f) (payloadBits_no_end _) v src []
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.aiUnary
   (RosserDirect.Append.machine (tokenBits (13))) machine (agree_aiUnary)
   (storage program [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simp only [embed_aiUnary] at h
 simpa [Membership.formulaPayload,unaryFormula,ZFR.TokenVM.emitFormula,payloadBits,
   List.flatMap_append,List.append_assoc] using h

theorem ai_move_run (f : ZFR.Formula) (v : Option Symbol)
    (program dst rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.aiMove .scan) v program dst [] (TypedContext.value (.formula f)) rows)
   (cfg (.aiMove .done) none program (TypedContext.value (.formula f) ++ dst) [] [] rows) := by
 have localRun := RosserDirect.move_frame (payloadBits (valueTokens (.formula f)))
   (payloadBits_no_end _) v [] dst
 have h := Routine.lift_embedded_run moveRoles move_injective Control.aiMove
   RosserDirect.machine machine agree_aiMove (storage program [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_aiMove,TypedContext.value,valueSymbols] using h


theorem agree_aiBuild (q : AllIntroPremise.Q) (h : AllIntroPremise.machine q ≠ .halt) :
 machine (.aiBuild q) = Routine.relocate quantPremiseRoles Control.aiBuild (AllIntroPremise.machine q) := by
 cases q <;> simp_all [machine,AllIntroPremise.machine]
theorem embed_aiBuild (q : AllIntroPremise.Q) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 FourStack.embed4 quantPremiseRoles Control.aiBuild (FourStack.cfg4 q v p tmp scr vals) (fun _ => rows) =
 cfg (.aiBuild q) v p vals scr tmp rows := by
 unfold FourStack.embed4 cfg FourStack.cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem ai_build_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.aiBuild (.save .scan)) v p vals [] (TypedContext.stack [.formula f,.context Γ]) rows)
 (cfg (.aiBuild .done) none p (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ vals) [] [] rows) := by
 have h := FourStack.lift4_run quantPremiseRoles quantPremise_injective Control.aiBuild
  AllIntroPremise.machine machine agree_aiBuild (fun _ => rows)
  (AllIntroPremise.construct Γ f v p [] vals) (by simp [FourStack.cfg4])
 simpa [embed_aiBuild,TypedContext.stack,List.append_assoc] using h

theorem ai_tag0 (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.aiTag0) v p (.bit1 :: .tokenEnd :: vals) [] [] rows) =
 some (cfg (.aiTag1) (some .bit1) p (.tokenEnd :: vals) [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem ai_tag1 (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.aiTag1) v p (.tokenEnd :: vals) [] [] rows) =
 some (cfg (.aiUnary .scan) (some .tokenEnd) p vals [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem ai_leave_unary (f : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine
   (cfg (.aiUnary .done) v p vals [] (Membership.formulaPayload f ++ [.frameEnd]) rows) =
 some (cfg (.aiMove .scan) v p vals [] (TypedContext.value (.formula f)) rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage,formula_value]
 funext k; cases k <;> rfl


theorem ai_test_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
 (rest vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 47 ++ rest) (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.aiCompare .tag) none rest (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals)) [] [] rows) := by
 let vs := TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals
 obtain ⟨w,hd⟩ := dispatch_run 23 v rest vs [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 23)) w rest vs [] [] rows)
  (cfg (.aiCopy (.scan (.run 1 .start))) w rest vs [] [] rows) := global_step rfl
 have hc := Routine.lift_embedded_run constructRoles construct_injective Control.aiCopy TypedBlock.machine machine agree_aiCopy (storage rest [] [] [] rows)
  (TypedBlock.copy_block 1 [.formula f,.context Γ] rfl w vals []) (by simp [config])
 simp only [embed_aiCopy] at hc
 have hl : TM2.Reaches machine (cfg (.aiCopy .done) none rest vs [] (TypedContext.stack [.formula f,.context Γ]) rows)
  (cfg (.aiBuild (.save .scan)) none rest vs [] (TypedContext.stack [.formula f,.context Γ]) rows) := global_step rfl
 have hb := ai_build_run Γ f none rest vs rows
 have hr : TM2.Reaches machine (cfg (.aiBuild .done) none rest (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ vs) [] [] rows)
  (cfg (.aiCompare .tag) none rest (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ vs) [] [] rows) := global_step rfl
 simp only [TM2.Reaches,vs,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hl hb hr ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hr))))

theorem ai_result_run (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
 (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg .aiTag0 v p (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.dispatch .start) none p vals [] [] (FramedRow.encode (.seq Γ (.all f)) ++ rows)) := by
 let tail := TypedContext.value (.context Γ) ++ vals
 have h0 := global_step (ai_tag0 v p (Membership.formulaPayload f ++ .frameEnd :: tail) rows)
 have h1 := global_step (ai_tag1 (some .bit1) p (Membership.formulaPayload f ++ .frameEnd :: tail) rows)
 have hc := ai_unary_run f (some .tokenEnd) p tail rows
 have hl := global_step (ai_leave_unary (.all f) none p tail rows)
 have hm := ai_move_run (.all f) none p tail rows
 have he : TM2.Reaches machine
  (cfg (.aiMove .done) none p (TypedContext.value (.formula (.all f)) ++ tail) [] [] rows)
  (cfg (.aiResult (.formula0 0)) none p (TypedContext.value (.formula (.all f)) ++ tail) [] [] rows) := global_step rfl
 have hr := Routine.lift_embedded_run rowRoles row_injective Control.aiResult (FramedRowConstructor.machine false) machine agree_aiResult (storage p [] [] [] [])
  (FramedRowConstructor.construct_seq_raw Γ (.all f) none vals rows) (by simp [config])
 simp only [embed_aiResult] at hr
 have hf : TM2.Reaches machine (cfg (.aiResult .done) none p vals [] [] (FramedRow.encode (.seq Γ (.all f)) ++ rows))
  (cfg (.dispatch .start) none p vals [] [] (FramedRow.encode (.seq Γ (.all f)) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,tail,formula_value,List.append_assoc,List.cons_append,List.singleton_append] at h0 h1 hc hl hm he hr hf ⊢
 exact h0.trans (h1.trans (hc.trans (hl.trans (hm.trans (he.trans (hr.trans hf))))))

theorem execute_allI (Γ : ZFR.Context) (f : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 47 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.all f)) ++ rows)) := by
 let vs := TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s
 have ht := ai_test_run Γ f v rest (TypedContext.stack s) (FramedRow.encode (.seq (ZFR.shiftContext Γ) f) ++ rows)
 obtain ⟨w,h⟩ := FramedRowEquality.equal_rows_exact (.seq (ZFR.shiftContext Γ) f) none vs [] rows
 have hc := Routine.lift_embedded_run rowRoles row_injective Control.aiCompare FramedRowEquality.machine machine agree_aiCompare (storage rest [] [] [] []) h (by simp [config])
 simp only [embed_aiCompare] at hc
 have he : TM2.Reaches machine (cfg (.aiCompare .equal) w rest vs [] [] rows) (cfg .aiTag0 w rest vs [] [] rows) := global_step rfl
 have hr := ai_result_run Γ f w rest (TypedContext.stack s) rows
 simp only [TM2.Reaches,vs,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht hc he hr ⊢
 exact ht.trans (hc.trans (he.trans hr))
theorem reject_allI (Γ : ZFR.Context) (f : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq (ZFR.shiftContext Γ) f ≠ actual) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 47 ++ rest) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 let vs := TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s
 have ht := ai_test_run Γ f v rest (TypedContext.stack s) (FramedRow.encode actual ++ rows)
 obtain ⟨w,left,right,h⟩ := FramedRowEquality.compare_rows (.seq (ZFR.shiftContext Γ) f) actual none vs [] rows
 simp only [hne,↓reduceIte] at h
 have hc := Routine.lift_embedded_run rowRoles row_injective Control.aiCompare FramedRowEquality.machine machine agree_aiCompare (storage rest [] [] [] []) h (by simp [config])
 simp only [embed_aiCompare] at hc
 have he : TM2.Reaches machine (cfg (.aiCompare .different) w rest left [] [] right) (cfg .proofReject w rest left [] [] right) := global_step rfl
 refine ⟨w,left,right,?_⟩
 simpa [TM2.Reaches,vs,TypedContext.stack,List.append_assoc] using ht.trans (hc.trans he)
end RosserDirect.ContextProgram
