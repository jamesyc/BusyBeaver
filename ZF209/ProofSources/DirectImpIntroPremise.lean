module
public import DirectOperandSwap
public import DirectFramedRowConstructors
@[expose] public section
namespace RosserDirect.ImpIntroPremise
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | save (q : Grammar.CopyControl TypedBlock.Control)
 | swapIn (q : OperandSwap.Control)
 | cons (q : TypedContext.Control)
 | swapOut (q : OperandSwap.Control)
 | row (q : FramedRowConstructor.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .save .done => .goto (fun _ => .swapIn (.first (.scan (.run 0 .start))))
 | .save q => Routine.relocate id Control.save ((TypedBlock.moveMachine) q)
 | .swapIn .done => .goto (fun _ => .cons .context0)
 | .swapIn q => Routine.relocate id Control.swapIn ((OperandSwap.machine) q)
 | .cons .done => .goto (fun _ => .swapOut (.first (.scan (.run 0 .start))))
 | .cons q => Routine.relocate id Control.cons ((TypedContext.machine) q)
 | .swapOut .done => .goto (fun _ => .row (.formula0 0))
 | .swapOut q => Routine.relocate SelectSecond.swap Control.swapOut ((OperandSwap.machine) q)
 | .row .done => .goto (fun _ => .done)
 | .row q => Routine.relocate SelectSecond.swap Control.row ((FramedRowConstructor.machine false) q)
 | .done => .halt

theorem agree_save (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.save q) = Routine.relocate id Control.save ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_save (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.save (config q v a b c) (fun _ => []) = config (.save q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swapIn (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swapIn q) = Routine.relocate id Control.swapIn ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swapIn (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.swapIn (config q v a b c) (fun _ => []) = config (.swapIn q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_cons (q : TypedContext.Control) (h : (TypedContext.machine) q ≠ .halt) :
 machine (.cons q) = Routine.relocate id Control.cons ((TypedContext.machine) q) := by
 cases q <;> simp_all [machine,TypedContext.machine]

theorem embed_cons (q : TypedContext.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.cons (config q v a b c) (fun _ => []) = config (.cons q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swapOut (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swapOut q) = Routine.relocate SelectSecond.swap Control.swapOut ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swapOut (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.swapOut (config q v a b c) (fun _ => []) = config (.swapOut q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_row (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.row q) = Routine.relocate SelectSecond.swap Control.row ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_row (q : FramedRowConstructor.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.row (config q v a b c) (fun _ => []) = config (.row q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Build the exact expected implication-introduction premise (a :: Γ) ⊢ b.
The result is on the input stack; the other stack is restored exactly. -/
theorem construct (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (src dst : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (config (.save (.scan (.run 0 .start))) v (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst))
 (config .done none (FramedRow.encode (.seq (a :: Γ) b) ++ TypedContext.stack src) [] (TypedContext.stack dst)) := by
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.save TypedBlock.moveMachine machine agree_save (fun _ => [])
   (TypedBlock.move_block 0 [.formula b] rfl v (TypedContext.stack (.formula a :: .context Γ :: src)) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_save] at h0
 have l0 : TM2.Reaches machine
   (config (.save .done) none (TypedContext.stack (.formula a :: .context Γ :: src)) [] (TypedContext.stack (.formula b :: dst)))
   (config (.swapIn (.first (.scan (.run 0 .start)))) none (TypedContext.stack (.formula a :: .context Γ :: src)) [] (TypedContext.stack (.formula b :: dst))) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run id Function.injective_id Control.swapIn OperandSwap.machine machine agree_swapIn (fun _ => [])
   (OperandSwap.swap_fields (.context Γ) (.formula a) none (TypedContext.stack src) (TypedContext.stack (.formula b :: dst))) (by simp [config])
 simp only [embed_swapIn] at h1
 have l1 : TM2.Reaches machine
   (config (.swapIn .done) none (TypedContext.stack (.context Γ :: .formula a :: src)) [] (TypedContext.stack (.formula b :: dst)))
   (config (.cons .context0) none (TypedContext.stack (.context Γ :: .formula a :: src)) [] (TypedContext.stack (.formula b :: dst))) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Control.cons TypedContext.machine machine agree_cons (fun _ => [])
   (TypedContext.cons_typed a Γ none src (.formula b :: dst)) (by simp [config])
 simp only [embed_cons] at h2
 have l2 : TM2.Reaches machine
   (config (.cons .done) none (TypedContext.stack src) [] (TypedContext.stack (.context (a :: Γ) :: .formula b :: dst)))
   (config (.swapOut (.first (.scan (.run 0 .start)))) none (TypedContext.stack src) [] (TypedContext.stack (.context (a :: Γ) :: .formula b :: dst))) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.swapOut OperandSwap.machine machine agree_swapOut (fun _ => [])
   (OperandSwap.swap_fields (.formula b) (.context (a :: Γ)) none (TypedContext.stack dst) (TypedContext.stack src)) (by simp [config])
 simp only [embed_swapOut] at h3
 have l3 : TM2.Reaches machine
   (config (.swapOut .done) none (TypedContext.stack src) [] (TypedContext.stack (.formula b :: .context (a :: Γ) :: dst)))
   (config (.row (.formula0 0)) none (TypedContext.stack src) [] (TypedContext.stack (.formula b :: .context (a :: Γ) :: dst))) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.row (FramedRowConstructor.machine false) machine agree_row (fun _ => [])
   (FramedRowConstructor.construct_seq (a :: Γ) b none dst (TypedContext.stack src)) (by simp [config])
 simp only [embed_row] at h4
 have l4 : TM2.Reaches machine
   (config (.row .done) none (FramedRow.encode (.seq (a :: Γ) b) ++ TypedContext.stack src) [] (TypedContext.stack dst))
   (config .done none (FramedRow.encode (.seq (a :: Γ) b) ++ TypedContext.stack src) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans l4))))))))

end RosserDirect.ImpIntroPremise
