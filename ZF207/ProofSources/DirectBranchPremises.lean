module
public import DirectRawPremiseBuilder
public import DirectFramedRowMove
@[expose] public section
namespace RosserDirect.BranchPremises
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | selectOut (q : SelectSecond.Control)
 | premiseA (q : ImpIntroPremise.Control)
 | saveC (q : Grammar.CopyControl TypedBlock.Control)
 | selectIn (q : SelectSecond.Control)
 | restoreC (q : Grammar.CopyControl TypedBlock.Control)
 | premiseB (q : ImpIntroPremise.Control)
 | moveB (q : Grammar.CopyControl FramedRowEquality.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy .done => .goto (fun _ => .selectOut (.save .scan))
 | .copy q => Routine.relocate id Control.copy ((TypedBlock.machine) q)
 | .selectOut .done => .goto (fun _ => .premiseA (.save (.scan (.run 0 .start))))
 | .selectOut q => Routine.relocate SelectSecond.swap Control.selectOut ((SelectSecond.machine) q)
 | .premiseA .done => .goto (fun _ => .saveC (.scan (.run 0 .start)))
 | .premiseA q => Routine.relocate SelectSecond.swap Control.premiseA ((ImpIntroPremise.machine) q)
 | .saveC .done => .goto (fun _ => .selectIn (.save .scan))
 | .saveC q => Routine.relocate id Control.saveC ((TypedBlock.moveMachine) q)
 | .selectIn .done => .goto (fun _ => .restoreC (.scan (.run 0 .start)))
 | .selectIn q => Routine.relocate id Control.selectIn ((SelectSecond.machine) q)
 | .restoreC .done => .goto (fun _ => .premiseB (.save (.scan (.run 0 .start))))
 | .restoreC q => Routine.relocate SelectSecond.swap Control.restoreC ((TypedBlock.moveMachine) q)
 | .premiseB .done => .goto (fun _ => .moveB (.scan .tag))
 | .premiseB q => Routine.relocate id Control.premiseB ((ImpIntroPremise.machine) q)
 | .moveB .done => .goto (fun _ => .done)
 | .moveB q => Routine.relocate id Control.moveB ((FramedRowMove.machine) q)
 | .done => .halt

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Control.copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy (config q v a b c) (fun _ => []) = config (.copy q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_selectOut (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.selectOut q) = Routine.relocate SelectSecond.swap Control.selectOut ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_selectOut (q : SelectSecond.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.selectOut (config q v a b c) (fun _ => []) = config (.selectOut q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_premiseA (q : ImpIntroPremise.Control) (h : (ImpIntroPremise.machine) q ≠ .halt) :
 machine (.premiseA q) = Routine.relocate SelectSecond.swap Control.premiseA ((ImpIntroPremise.machine) q) := by
 cases q <;> simp_all [machine,ImpIntroPremise.machine]

theorem embed_premiseA (q : ImpIntroPremise.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.premiseA (config q v a b c) (fun _ => []) = config (.premiseA q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_saveC (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.saveC q) = Routine.relocate id Control.saveC ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_saveC (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.saveC (config q v a b c) (fun _ => []) = config (.saveC q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_selectIn (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.selectIn q) = Routine.relocate id Control.selectIn ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_selectIn (q : SelectSecond.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.selectIn (config q v a b c) (fun _ => []) = config (.selectIn q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_restoreC (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.restoreC q) = Routine.relocate SelectSecond.swap Control.restoreC ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_restoreC (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.restoreC (config q v a b c) (fun _ => []) = config (.restoreC q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_premiseB (q : ImpIntroPremise.Control) (h : (ImpIntroPremise.machine) q ≠ .halt) :
 machine (.premiseB q) = Routine.relocate id Control.premiseB ((ImpIntroPremise.machine) q) := by
 cases q <;> simp_all [machine,ImpIntroPremise.machine]

theorem embed_premiseB (q : ImpIntroPremise.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.premiseB (config q v a b c) (fun _ => []) = config (.premiseB q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_moveB (q : Grammar.CopyControl FramedRowEquality.Control) (h : (FramedRowMove.machine) q ≠ .halt) :
 machine (.moveB q) = Routine.relocate id Control.moveB ((FramedRowMove.machine) q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]

theorem embed_moveB (q : Grammar.CopyControl FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.moveB (config q v a b c) (fun _ => []) = config (.moveB q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev field (a : ZFR.Formula) := TypedContext.value (.formula a)
abbrev context (Γ : ZFR.Context) := TypedContext.value (.context Γ)

/-- Exact branch premise pair in stack order, preserving arbitrary raw tails. -/
theorem construct (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 3 .start))) v (field c ++ field b ++ field a ++ context Γ ++ src) [] dst)
 (config .done none src [] (FramedRow.encode (.seq (b :: Γ) c) ++ FramedRow.encode (.seq (a :: Γ) c) ++ dst)) := by
 let orig := field c ++ field b ++ field a ++ context Γ ++ src
 let ra := FramedRow.encode (.seq (a :: Γ) c)
 let rb := FramedRow.encode (.seq (b :: Γ) c)
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 3 [.formula c,.formula b,.formula a,.context Γ] rfl v src dst) (by simp [config])
 simp only [embed_copy] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none orig [] (field c ++ field b ++ field a ++ context Γ ++ dst))
   (config (.selectOut (.save .scan)) none orig [] (field c ++ field b ++ field a ++ context Γ ++ dst)) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.selectOut SelectSecond.machine machine agree_selectOut (fun _ => [])
   (SelectSecond.select_second (.formula b) c none (field a ++ context Γ ++ dst) orig) (by simp [config])
 simp only [embed_selectOut] at h1
 have l1 : TM2.Reaches machine
   (config (.selectOut .done) none orig [] (field c ++ field a ++ context Γ ++ dst))
   (config (.premiseA (.save (.scan (.run 0 .start)))) none orig [] (field c ++ field a ++ context Γ ++ dst)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.premiseA ImpIntroPremise.machine machine agree_premiseA (fun _ => [])
   (ImpIntroPremise.construct_raw Γ a c none dst orig) (by simp [config])
 simp only [embed_premiseA] at h2
 have l2 : TM2.Reaches machine
   (config (.premiseA .done) none orig [] (ra ++ dst))
   (config (.saveC (.scan (.run 0 .start))) none orig [] (ra ++ dst)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.saveC TypedBlock.moveMachine machine agree_saveC (fun _ => [])
   (TypedBlock.move_block 0 [.formula c] rfl none (field b ++ field a ++ context Γ ++ src) (ra ++ dst)) (by simp [config])
 simp only [embed_saveC] at h3
 have l3 : TM2.Reaches machine
   (config (.saveC .done) none (field b ++ field a ++ context Γ ++ src) [] (field c ++ ra ++ dst))
   (config (.selectIn (.save .scan)) none (field b ++ field a ++ context Γ ++ src) [] (field c ++ ra ++ dst)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run id Function.injective_id Control.selectIn SelectSecond.machine machine agree_selectIn (fun _ => [])
   (SelectSecond.select_second (.formula a) b none (context Γ ++ src) (field c ++ ra ++ dst)) (by simp [config])
 simp only [embed_selectIn] at h4
 have l4 : TM2.Reaches machine
   (config (.selectIn .done) none (field b ++ context Γ ++ src) [] (field c ++ ra ++ dst))
   (config (.restoreC (.scan (.run 0 .start))) none (field b ++ context Γ ++ src) [] (field c ++ ra ++ dst)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.restoreC TypedBlock.moveMachine machine agree_restoreC (fun _ => [])
   (TypedBlock.move_block 0 [.formula c] rfl none (ra ++ dst) (field b ++ context Γ ++ src)) (by simp [config])
 simp only [embed_restoreC] at h5
 have l5 : TM2.Reaches machine
   (config (.restoreC .done) none (field c ++ field b ++ context Γ ++ src) [] (ra ++ dst))
   (config (.premiseB (.save (.scan (.run 0 .start)))) none (field c ++ field b ++ context Γ ++ src) [] (ra ++ dst)) := Relation.ReflTransGen.single rfl
 have h6 := Routine.lift_embedded_run id Function.injective_id Control.premiseB ImpIntroPremise.machine machine agree_premiseB (fun _ => [])
   (ImpIntroPremise.construct_raw Γ b c none src (ra ++ dst)) (by simp [config])
 simp only [embed_premiseB] at h6
 have l6 : TM2.Reaches machine
   (config (.premiseB .done) none (rb ++ src) [] (ra ++ dst))
   (config (.moveB (.scan .tag)) none (rb ++ src) [] (ra ++ dst)) := Relation.ReflTransGen.single rfl
 have h7 := Routine.lift_embedded_run id Function.injective_id Control.moveB FramedRowMove.machine machine agree_moveB (fun _ => [])
   (FramedRowMove.move_row (.seq (b :: Γ) c) none src (ra ++ dst)) (by simp [config])
 simp only [embed_moveB] at h7
 have l7 : TM2.Reaches machine
   (config (.moveB .done) none src [] (rb ++ ra ++ dst))
   (config .done none src [] (rb ++ ra ++ dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,orig,ra,rb,field,context,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 h7 l7 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans (l6.trans (h7.trans l7))))))))))))))

end RosserDirect.BranchPremises
