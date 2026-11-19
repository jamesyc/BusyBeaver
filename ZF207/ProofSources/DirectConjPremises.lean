module
public import DirectFramedRowMove
public import DirectOperandSwap
public import DirectFramedRowConstructors
@[expose] public section
namespace RosserDirect.ConjPremises
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | drop (q : Grammar.DropControl TypedBlock.Control)
 | rowA (q : FramedRowConstructor.Control)
 | moveRow (q : Grammar.CopyControl FramedRowEquality.Control)
 | select (q : SelectSecond.Control)
 | rowB (q : FramedRowConstructor.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy .done => .goto (fun _ => .drop (.scan (.run 0 .start)))
 | .copy q => Routine.relocate id Control.copy ((TypedBlock.machine) q)
 | .drop .done => .goto (fun _ => .rowA (.formula0 0))
 | .drop q => Routine.relocate SelectSecond.swap Control.drop ((TypedBlock.dropMachine) q)
 | .rowA .done => .goto (fun _ => .moveRow (.scan .tag))
 | .rowA q => Routine.relocate SelectSecond.swap Control.rowA ((FramedRowConstructor.machine false) q)
 | .moveRow .done => .goto (fun _ => .select (.save .scan))
 | .moveRow q => Routine.relocate id Control.moveRow ((FramedRowMove.machine) q)
 | .select .done => .goto (fun _ => .rowB (.formula0 0))
 | .select q => Routine.relocate id Control.select ((SelectSecond.machine) q)
 | .rowB .done => .goto (fun _ => .done)
 | .rowB q => Routine.relocate id Control.rowB ((FramedRowConstructor.machine false) q)
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

theorem agree_drop (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.drop q) = Routine.relocate SelectSecond.swap Control.drop ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_drop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.drop (config q v a b c) (fun _ => []) = config (.drop q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_rowA (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.rowA q) = Routine.relocate SelectSecond.swap Control.rowA ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_rowA (q : FramedRowConstructor.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.rowA (config q v a b c) (fun _ => []) = config (.rowA q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_moveRow (q : Grammar.CopyControl FramedRowEquality.Control) (h : (FramedRowMove.machine) q ≠ .halt) :
 machine (.moveRow q) = Routine.relocate id Control.moveRow ((FramedRowMove.machine) q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]

theorem embed_moveRow (q : Grammar.CopyControl FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.moveRow (config q v a b c) (fun _ => []) = config (.moveRow q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_select (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.select q) = Routine.relocate id Control.select ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_select (q : SelectSecond.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.select (config q v a b c) (fun _ => []) = config (.select q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_rowB (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.rowB q) = Routine.relocate id Control.rowB ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_rowB (q : FramedRowConstructor.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.rowB (config q v a b c) (fun _ => []) = config (.rowB q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Construct the two exact premises in VM stack order, Γ ⊢ b above Γ ⊢ a. -/
theorem construct (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (src dst : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst))
 (config .done none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ b) ++ FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) := by
 let orig := .formula b :: .formula a :: .context Γ :: src
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 2 [.formula b,.formula a,.context Γ] rfl v (TypedContext.stack src) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_copy] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none (TypedContext.stack orig) [] (TypedContext.stack (.formula b :: .formula a :: .context Γ :: dst)))
   (config (.drop (.scan (.run 0 .start))) none (TypedContext.stack orig) [] (TypedContext.stack (.formula b :: .formula a :: .context Γ :: dst))) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 0 [.formula b] rfl none (TypedContext.stack (.formula a :: .context Γ :: dst)) [] (TypedContext.stack orig)
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.drop TypedBlock.dropMachine machine agree_drop (fun _ => []) h (by simp [config])
 simp only [embed_drop] at h1
 have l1 : TM2.Reaches machine
   (config (.drop .done) w (TypedContext.stack orig) [] (TypedContext.stack (.formula a :: .context Γ :: dst)))
   (config (.rowA (.formula0 0)) w (TypedContext.stack orig) [] (TypedContext.stack (.formula a :: .context Γ :: dst))) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.rowA (FramedRowConstructor.machine false) machine agree_rowA (fun _ => [])
   (FramedRowConstructor.construct_seq Γ a w dst (TypedContext.stack orig)) (by simp [config])
 simp only [embed_rowA] at h2
 have l2 : TM2.Reaches machine
   (config (.rowA .done) none (FramedRow.encode (.seq Γ a) ++ TypedContext.stack orig) [] (TypedContext.stack dst))
   (config (.moveRow (.scan .tag)) none (FramedRow.encode (.seq Γ a) ++ TypedContext.stack orig) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.moveRow FramedRowMove.machine machine agree_moveRow (fun _ => [])
   (FramedRowMove.move_row (.seq Γ a) none (TypedContext.stack orig) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_moveRow] at h3
 have l3 : TM2.Reaches machine
   (config (.moveRow .done) none (TypedContext.stack orig) [] (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst))
   (config (.select (.save .scan)) none (TypedContext.stack orig) [] (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run id Function.injective_id Control.select SelectSecond.machine machine agree_select (fun _ => [])
   (SelectSecond.select_second (.formula a) b none (TypedContext.stack (.context Γ :: src)) (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) (by simp [config])
 simp only [embed_select] at h4
 have l4 : TM2.Reaches machine
   (config (.select .done) none (TypedContext.stack (.formula b :: .context Γ :: src)) [] (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst))
   (config (.rowB (.formula0 0)) none (TypedContext.stack (.formula b :: .context Γ :: src)) [] (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run id Function.injective_id Control.rowB (FramedRowConstructor.machine false) machine agree_rowB (fun _ => [])
   (FramedRowConstructor.construct_seq Γ b none src (FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) (by simp [config])
 simp only [embed_rowB] at h5
 have l5 : TM2.Reaches machine
   (config (.rowB .done) none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ b) ++ FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst))
   (config .done none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ b) ++ FramedRow.encode (.seq Γ a) ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,orig,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans l5))))))))))

end RosserDirect.ConjPremises
