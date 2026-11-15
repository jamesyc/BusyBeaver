module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_iiCopy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.iiCopy q) = Routine.relocate constructRoles Control.iiCopy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_iiCopy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.iiCopy (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.iiCopy q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_iiBuild (q : ImpIntroPremise.Control) (h : (ImpIntroPremise.machine) q ≠ .halt) :
 machine (.iiBuild q) = Routine.relocate moveRoles Control.iiBuild ((ImpIntroPremise.machine) q) := by
 cases q <;> simp_all [machine,ImpIntroPremise.machine]

theorem embed_iiBuild (q : ImpIntroPremise.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.iiBuild (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.iiBuild q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_iiCompare (q : FramedRowEquality.Control) (h : (FramedRowEquality.machine) q ≠ .halt) :
 machine (.iiCompare q) = Routine.relocate premiseRoles Control.iiCompare ((FramedRowEquality.machine) q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_iiCompare (q : FramedRowEquality.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed premiseRoles Control.iiCompare (config q v tmp scr rows) (storage p vals [] [] []) =
 cfg (.iiCompare q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_iiBinary (q : Binary.Control) (h : (Binary.machine 11) q ≠ .halt) :
 machine (.iiBinary q) = Routine.relocate constructRoles Control.iiBinary ((Binary.machine 11) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_iiBinary (q : Binary.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.iiBinary (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.iiBinary q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl
theorem ii_copy_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.iiCopy (.scan (.run 2 .start))) v p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.iiCopy .done) none p (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.iiCopy
   TypedBlock.machine machine agree_iiCopy (storage p [] [] [] rows)
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack s) []) (by simp [config])
 simpa [embed_iiCopy,TypedContext.stack,List.append_assoc] using h


theorem ii_build_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (p rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.iiBuild (.save (.scan (.run 0 .start)))) v p (TypedContext.stack s) [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
 (cfg (.iiBuild .done) none p (TypedContext.stack s) [] (FramedRow.encode (.seq (a :: Γ) b)) rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.iiBuild
   ImpIntroPremise.machine machine agree_iiBuild (storage p [] [] [] rows)
   (ImpIntroPremise.construct Γ a b v [] s) (by simp [config])
 simpa [embed_iiBuild,TypedContext.stack] using h

theorem ii_equal_run (r : ZFR.Row) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w, TM2.Reaches machine
 (cfg (.iiCompare .tag) v p vals [] (FramedRow.encode r) (FramedRow.encode r ++ rows))
 (cfg (.iiCompare .equal) w p vals [] [] rows) := by
 obtain ⟨w,hw⟩ := FramedRowEquality.equal_rows_exact r v [] [] rows
 have h := Routine.lift_embedded_run premiseRoles premise_injective Control.iiCompare
   FramedRowEquality.machine machine agree_iiCompare (storage p vals [] [] []) hw (by simp [config])
 exact ⟨w,by simpa [embed_iiCompare] using h⟩

theorem ii_different_run (r t : ZFR.Row) (hne : r ≠ t) (v : Option Symbol) (p vals rows : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.iiCompare .tag) v p vals [] (FramedRow.encode r) (FramedRow.encode t ++ rows))
 (cfg (.iiCompare .different) w p vals [] left right) := by
 obtain ⟨w,left,right,hw⟩ := FramedRowEquality.compare_rows r t v [] [] rows
 simp only [hne,↓reduceIte] at hw
 have h := Routine.lift_embedded_run premiseRoles premise_injective Control.iiCompare
   FramedRowEquality.machine machine agree_iiCompare (storage p vals [] [] []) hw (by simp [config])
 exact ⟨w,left,right,by simpa [embed_iiCompare] using h⟩

theorem ii_binary_run (a b : ZFR.Formula) (v : Option Symbol) (p src rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.iiBinary .boot) v p (TypedContext.value (.formula b) ++ TypedContext.value (.formula a) ++ src) [] [] rows)
 (cfg (.iiBinary .done) none p src [] (TypedContext.value (.formula (.imp a b))) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.iiBinary
   (Binary.machine 11) machine agree_iiBinary (storage p [] [] [] rows)
   (binary_local 2 a b v src []) (by simp [config])
 simpa [embed_iiBinary,binaryFormula] using h

theorem ii_test_run (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 25 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.iiCompare .tag) none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] (FramedRow.encode (.seq (a :: Γ) b)) rows) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 obtain ⟨w,hd⟩ := dispatch_run 12 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 12)) w rest vals [] [] rows)
   (cfg (.iiCopy (.scan (.run 2 .start))) w rest vals [] [] rows) := global_step rfl
 have hc := ii_copy_run Γ a b w rest rows s
 have hl : TM2.Reaches machine
   (cfg (.iiCopy .done) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows)
   (cfg (.iiBuild (.save (.scan (.run 0 .start)))) none rest vals [] (TypedContext.stack [.formula b,.formula a,.context Γ]) rows) := global_step rfl
 have hb := ii_build_run Γ a b none rest rows (.formula b :: .formula a :: .context Γ :: s)
 have hbl : TM2.Reaches machine
   (cfg (.iiBuild .done) none rest vals [] (FramedRow.encode (.seq (a :: Γ) b)) rows)
   (cfg (.iiCompare .tag) none rest vals [] (FramedRow.encode (.seq (a :: Γ) b)) rows) := global_step rfl
 exact hd.trans (he.trans (hc.trans (hl.trans (hb.trans hbl))))
theorem execute_ii (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 25 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode (.seq (a :: Γ) b) ++ rows))
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.imp a b)) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let suffix := TypedContext.stack (.context Γ :: s)
 have ht := ii_test_run Γ a b v rest (FramedRow.encode (.seq (a :: Γ) b) ++ rows) s
 obtain ⟨w,he⟩ := ii_equal_run (.seq (a :: Γ) b) none rest vals rows
 have ha : TM2.Reaches machine (cfg (.iiCompare .equal) w rest vals [] [] rows)
   (cfg (.iiBinary .boot) w rest vals [] [] rows) := global_step rfl
 have hb := ii_binary_run a b w rest suffix rows
 have hbl : TM2.Reaches machine
   (cfg (.iiBinary .done) none rest suffix [] (TypedContext.value (.formula (.imp a b))) rows)
   (cfg (.diMove .scan) none rest suffix [] (TypedContext.value (.formula (.imp a b))) rows) := global_step rfl
 have hm := di_move_run (.imp a b) none rest suffix rows
 have hml : TM2.Reaches machine
   (cfg (.diMove .done) none rest (TypedContext.value (.formula (.imp a b)) ++ suffix) [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest (TypedContext.value (.formula (.imp a b)) ++ suffix) [] [] rows) := global_step rfl
 have hr := di_result_run Γ (.imp a b) none rest rows s
 have hl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.imp a b)) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.imp a b)) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,suffix,TypedContext.stack,List.flatMap_cons,List.append_assoc] at ht he ha hb hbl hm hml hr hl ⊢
 exact ht.trans (he.trans (ha.trans (hb.trans (hbl.trans (hm.trans (hml.trans (hr.trans hl)))))))


theorem reject_ii (Γ : ZFR.Context) (a b : ZFR.Formula) (actual : ZFR.Row)
 (hne : ZFR.Row.seq (a :: Γ) b ≠ actual) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 ∃ w left right, TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 25 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] (FramedRow.encode actual ++ rows))
 (cfg .proofReject w rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] left right) := by
 have ht := ii_test_run Γ a b v rest (FramedRow.encode actual ++ rows) s
 obtain ⟨w,left,right,he⟩ := ii_different_run (.seq (a :: Γ) b) actual hne none rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) rows
 have hl : TM2.Reaches machine (cfg (.iiCompare .different) w rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] left right)
   (cfg .proofReject w rest (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] left right) := global_step rfl
 exact ⟨w,left,right,ht.trans (he.trans hl)⟩
end RosserDirect.ContextProgram
