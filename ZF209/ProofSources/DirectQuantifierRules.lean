module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def qePremise (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) : ZFR.Row :=
 .seq Γ (if k then ZFR.subst t f else .all f)
def qeResult (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) : ZFR.Row :=
 .seq Γ (if k then .ex f else ZFR.subst t f)
theorem agree_qeCopy (k : Bool) (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.qeCopy k q) = Routine.relocate constructRoles (Control.qeCopy k) (TypedBlock.machine q) := by
 cases k <;> cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem embed_qeCopy (k : Bool) (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles (Control.qeCopy k) (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.qeCopy k q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem agree_qeCompare (k : Bool) (q : FramedRowEquality.Control) (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.qeCompare k q) = Routine.relocate rowRoles (Control.qeCompare k) (FramedRowEquality.machine q) := by
 cases k <;> cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]
theorem embed_qeCompare (k : Bool) (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr rows : List Symbol) :
 Routine.embed rowRoles (Control.qeCompare k) (config q v vals scr rows) (storage p [] [] [] []) =
 cfg (.qeCompare k q) v p vals scr [] rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem agree_qeSubst_expected q (h : SubstitutionRow.machine q ≠ .halt) :
 machine (.qeSubst true q) = Routine.relocate quantPremiseRoles (Control.qeSubst true) (SubstitutionRow.machine q) := by
 cases q <;> simp_all [machine,SubstitutionRow.machine]
theorem embed_qeSubst_expected q v (p vals scr tmp rows : List Symbol) :
 FourStack.embed4 quantPremiseRoles (Control.qeSubst true) (FourStack.cfg4 q v p tmp scr vals) (fun _ => rows) =
 cfg (.qeSubst true q) v p vals scr tmp rows := by
 unfold FourStack.embed4 FourStack.cfg4 cfg
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem agree_qeUnary_expected q (h : QuantifierRow.machine false q ≠ .halt) :
 machine (.qeUnary true q) = Routine.relocate moveRoles (Control.qeUnary true) (QuantifierRow.machine false q) := by
 cases q <;> simp_all [machine,QuantifierRow.machine]
theorem embed_qeUnary_expected q v (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles (Control.qeUnary true) (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.qeUnary true q) v p vals scr tmp rows := by
 unfold Routine.embed config cfg
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem qeSubst_expected_run (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeSubst true (.swap (.first (.scan (.run 0 .start))))) v p vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows)
 (cfg (.qeSubst true .done) none p (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ vals) [] [] rows) := by
 have h := FourStack.lift4_run quantPremiseRoles quantPremise_injective (Control.qeSubst true) SubstitutionRow.machine machine agree_qeSubst_expected (fun _ => rows)
  (SubstitutionRow.substituted_row Γ f t v p [] vals) (by simp [FourStack.cfg4])
 simpa [embed_qeSubst_expected,TypedContext.stack,List.append_assoc] using h
theorem qeUnary_expected_run (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeUnary true (.drop (.scan (.run 0 .start)))) v p vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows)
 (cfg (.qeUnary true .done) none p (FramedRow.encode (.seq Γ (.all f)) ++ vals) [] [] rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective (Control.qeUnary true) (QuantifierRow.machine false) machine agree_qeUnary_expected (storage p [] [] [] rows)
  (QuantifierRow.construct false Γ f t v [] vals) (by simp [config])
 simpa [embed_qeUnary_expected,QuantifierRow.quantified,TypedContext.stack,List.append_assoc] using h
theorem agree_qeSubst_result q (h : SubstitutionRow.machine q ≠ .halt) :
 machine (.qeSubst false q) = Routine.relocate quantResultRoles (Control.qeSubst false) (SubstitutionRow.machine q) := by
 cases q <;> simp_all [machine,SubstitutionRow.machine]
theorem embed_qeSubst_result q v (p vals scr tmp rows : List Symbol) :
 FourStack.embed4 quantResultRoles (Control.qeSubst false) (FourStack.cfg4 q v p vals scr rows) (fun _ => tmp) =
 cfg (.qeSubst false q) v p vals scr tmp rows := by
 unfold FourStack.embed4 FourStack.cfg4 cfg
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem agree_qeUnary_result q (h : QuantifierRow.machine true q ≠ .halt) :
 machine (.qeUnary false q) = Routine.relocate rowRoles (Control.qeUnary false) (QuantifierRow.machine true q) := by
 cases q <;> simp_all [machine,QuantifierRow.machine]
theorem embed_qeUnary_result q v (p vals scr tmp rows : List Symbol) :
 Routine.embed rowRoles (Control.qeUnary false) (config q v vals scr rows) (storage p [] [] tmp []) =
 cfg (.qeUnary false q) v p vals scr tmp rows := by
 unfold Routine.embed config cfg
 simp only [Option.map_some]
 congr 1
 funext j; cases j <;> rfl
theorem qeSubst_result_run (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeSubst false (.swap (.first (.scan (.run 0 .start))))) v p (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.qeSubst false .done) none p vals [] [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ rows)) := by
 have h := FourStack.lift4_run quantResultRoles quantResult_injective (Control.qeSubst false) SubstitutionRow.machine machine agree_qeSubst_result (fun _ => [])
  (SubstitutionRow.substituted_row Γ f t v p vals rows) (by simp [FourStack.cfg4])
 simpa [embed_qeSubst_result,TypedContext.stack,List.append_assoc] using h
theorem qeUnary_result_run (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeUnary false (.drop (.scan (.run 0 .start)))) v p (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.qeUnary false .done) none p vals [] [] (FramedRow.encode (.seq Γ (.ex f)) ++ rows)) := by
 have h := Routine.lift_embedded_run rowRoles row_injective (Control.qeUnary false) (QuantifierRow.machine true) machine agree_qeUnary_result (storage p [] [] [] [])
  (QuantifierRow.construct true Γ f t v vals rows) (by simp [config])
 simpa [embed_qeUnary_result,QuantifierRow.quantified,TypedContext.stack,List.append_assoc] using h



theorem qe_expected_run (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeCopy k .done) v rest vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows)
 (cfg (.qeCompare k .tag) none rest (FramedRow.encode (qePremise k Γ f t) ++ vals) [] [] rows) := by
 cases k
 · have he : TM2.Reaches machine
    (cfg (.qeCopy false .done) v rest vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows)
    (cfg (.qeUnary true (.drop (.scan (.run 0 .start)))) v rest vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows) := global_step rfl
   have h := qeUnary_expected_run Γ f t v rest vals rows
   have hr : TM2.Reaches machine
    (cfg (.qeUnary true .done) none rest (FramedRow.encode (.seq Γ (.all f)) ++ vals) [] [] rows)
    (cfg (.qeCompare false .tag) none rest (FramedRow.encode (.seq Γ (.all f)) ++ vals) [] [] rows) := global_step rfl
   exact he.trans (h.trans hr)
 · have he : TM2.Reaches machine
    (cfg (.qeCopy true .done) v rest vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows)
    (cfg (.qeSubst true (.swap (.first (.scan (.run 0 .start))))) v rest vals [] (TypedContext.stack [.nat t,.formula f,.context Γ]) rows) := global_step rfl
   have h := qeSubst_expected_run Γ f t v rest vals rows
   have hr : TM2.Reaches machine
    (cfg (.qeSubst true .done) none rest (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ vals) [] [] rows)
    (cfg (.qeCompare true .tag) none rest (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ vals) [] [] rows) := global_step rfl
   exact he.trans (h.trans hr)

theorem qe_test_run (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits (if k then 51 else 49) ++ rest)
  (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.qeCompare k .tag) none rest
  (FramedRow.encode (qePremise k Γ f t) ++ (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals)) [] [] rows) := by
 let vs := TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals
 obtain ⟨w,hd⟩ := dispatch_run (if k then 25 else 24) v rest vs [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode (if k then 25 else 24))) w rest vs [] [] rows)
  (cfg (.qeCopy k (.scan (.run 2 .start))) w rest vs [] [] rows) := by cases k <;> exact global_step rfl
 have hc := Routine.lift_embedded_run constructRoles construct_injective (Control.qeCopy k) TypedBlock.machine machine (agree_qeCopy k) (storage rest [] [] [] rows)
  (TypedBlock.copy_block 2 [.nat t,.formula f,.context Γ] rfl w vals []) (by simp [config])
 simp only [embed_qeCopy] at hc
 have hr := qe_expected_run k Γ f t none rest vs rows
 simp only [TM2.Reaches,vs,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd he hc hr ⊢
 have h := hd.trans (he.trans (hc.trans hr))
 cases k <;> exact h

theorem qe_result_run (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.qeCompare k .equal) v rest (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals) [] [] rows)
 (cfg (.dispatch .start) none rest vals [] [] (FramedRow.encode (qeResult k Γ f t) ++ rows)) := by
 let vs := TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ vals
 cases k
 · have he : TM2.Reaches machine (cfg (.qeCompare false .equal) v rest vs [] [] rows)
    (cfg (.qeSubst false (.swap (.first (.scan (.run 0 .start))))) v rest vs [] [] rows) := global_step rfl
   have h := qeSubst_result_run Γ f t v rest vals rows
   have hr : TM2.Reaches machine
    (cfg (.qeSubst false .done) none rest vals [] [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ rows))
    (cfg (.dispatch .start) none rest vals [] [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ rows)) := global_step rfl
   exact he.trans (h.trans hr)
 · have he : TM2.Reaches machine (cfg (.qeCompare true .equal) v rest vs [] [] rows)
    (cfg (.qeUnary false (.drop (.scan (.run 0 .start)))) v rest vs [] [] rows) := global_step rfl
   have h := qeUnary_result_run Γ f t v rest vals rows
   have hr : TM2.Reaches machine
    (cfg (.qeUnary false .done) none rest vals [] [] (FramedRow.encode (.seq Γ (.ex f)) ++ rows))
    (cfg (.dispatch .start) none rest vals [] [] (FramedRow.encode (.seq Γ (.ex f)) ++ rows)) := global_step rfl
   exact he.trans (h.trans hr)

theorem execute_quantifier (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits (if k then 51 else 49) ++ rest) (TypedContext.stack (.nat t :: .formula f :: .context Γ :: s)) [] [] (FramedRow.encode (qePremise k Γ f t) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (qeResult k Γ f t) ++ rows)) := by
 let vs := TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s
 have ht := qe_test_run k Γ f t v rest (TypedContext.stack s) (FramedRow.encode (qePremise k Γ f t) ++ rows)
 obtain ⟨w,h⟩ := FramedRowEquality.equal_rows_exact (qePremise k Γ f t) none vs [] rows
 have hc := Routine.lift_embedded_run rowRoles row_injective (Control.qeCompare k) FramedRowEquality.machine machine (agree_qeCompare k) (storage rest [] [] [] []) h (by simp [config])
 simp only [embed_qeCompare] at hc
 have hr := qe_result_run k Γ f t w rest (TypedContext.stack s) rows
 simp only [TM2.Reaches,vs,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht hc hr ⊢
 exact ht.trans (hc.trans hr)
theorem reject_quantifier (k : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat) (actual : ZFR.Row)
 (hne : qePremise k Γ f t ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits (if k then 51 else 49) ++ rest) (TypedContext.stack (.nat t :: .formula f :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest left [] [] right) := by
 let vs := TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ TypedContext.stack s
 have ht := qe_test_run k Γ f t v rest (TypedContext.stack s) (FramedRow.encode actual ++ rows)
 obtain ⟨w,left,right,h⟩ := FramedRowEquality.compare_rows (qePremise k Γ f t) actual none vs [] rows
 simp only [hne,↓reduceIte] at h
 have hc := Routine.lift_embedded_run rowRoles row_injective (Control.qeCompare k) FramedRowEquality.machine machine (agree_qeCompare k) (storage rest [] [] [] []) h (by simp [config])
 simp only [embed_qeCompare] at hc
 have he : TM2.Reaches machine (cfg (.qeCompare k .different) w rest left [] [] right) (cfg .proofReject w rest left [] [] right) := global_step rfl
 refine ⟨w,left,right,?_⟩
 simpa [TM2.Reaches,vs,TypedContext.stack,List.append_assoc] using ht.trans (hc.trans he)
end RosserDirect.ContextProgram
