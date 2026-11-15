module
public import DirectConjPremises
public import DirectPeirceConstructor
@[expose] public section
namespace RosserDirect.ImpElimPremises
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | imp (q : Binary.Control)
 | select (q : SelectSecond.Control)
 | swap (q : OperandSwap.Control)
 | pair (q : ConjPremises.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy .done => .goto (fun _ => .imp .boot)
 | .copy q => Routine.relocate id Control.copy ((TypedBlock.machine) q)
 | .imp .done => .goto (fun _ => .select (.save .scan))
 | .imp q => Routine.relocate SelectSecond.swap Control.imp ((Binary.machine 11) q)
 | .select .done => .goto (fun _ => .swap (.first (.scan (.run 0 .start))))
 | .select q => Routine.relocate id Control.select ((SelectSecond.machine) q)
 | .swap .done => .goto (fun _ => .pair (.copy (.scan (.run 2 .start))))
 | .swap q => Routine.relocate id Control.swap ((OperandSwap.machine) q)
 | .pair .done => .goto (fun _ => .done)
 | .pair q => Routine.relocate id Control.pair ((ConjPremises.machine) q)
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

theorem agree_imp (q : Binary.Control) (h : (Binary.machine 11) q ≠ .halt) :
 machine (.imp q) = Routine.relocate SelectSecond.swap Control.imp ((Binary.machine 11) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_imp (q : Binary.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.imp (config q v a b c) (fun _ => []) = config (.imp q) v c b a := by
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

theorem agree_swap (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swap q) = Routine.relocate id Control.swap ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swap (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.swap (config q v a b c) (fun _ => []) = config (.swap q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_pair (q : ConjPremises.Control) (h : (ConjPremises.machine) q ≠ .halt) :
 machine (.pair q) = Routine.relocate id Control.pair ((ConjPremises.machine) q) := by
 cases q <;> simp_all [machine,ConjPremises.machine]

theorem embed_pair (q : ConjPremises.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.pair (config q v a b c) (fun _ => []) = config (.pair q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Construct Γ ⊢ a above Γ ⊢ a → b, the exact premise order for modus ponens. -/
theorem construct (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (src dst : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 1 .start))) v (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst))
 (config .done none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ a) ++ FramedRow.encode (.seq Γ (.imp a b)) ++ TypedContext.stack dst)) := by
 let orig := .formula b :: .formula a :: .context Γ :: src
 let ab := ZFR.Formula.imp a b
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 1 [.formula b,.formula a] rfl v (TypedContext.stack (.context Γ :: src)) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_copy] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none (TypedContext.stack orig) [] (TypedContext.stack (.formula b :: .formula a :: dst)))
   (config (.imp .boot) none (TypedContext.stack orig) [] (TypedContext.stack (.formula b :: .formula a :: dst))) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.imp (Binary.machine 11) machine agree_imp (fun _ => [])
   (Peirce.imp_local a b none (TypedContext.stack dst) (TypedContext.stack orig)) (by simp [config])
 simp only [embed_imp] at h1
 have l1 : TM2.Reaches machine
   (config (.imp .done) none (TypedContext.stack (.formula ab :: orig)) [] (TypedContext.stack dst))
   (config (.select (.save .scan)) none (TypedContext.stack (.formula ab :: orig)) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Control.select SelectSecond.machine machine agree_select (fun _ => [])
   (SelectSecond.select_second (.formula b) ab none (TypedContext.stack (.formula a :: .context Γ :: src)) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_select] at h2
 have l2 : TM2.Reaches machine
   (config (.select .done) none (TypedContext.stack (.formula ab :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst))
   (config (.swap (.first (.scan (.run 0 .start)))) none (TypedContext.stack (.formula ab :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.swap OperandSwap.machine machine agree_swap (fun _ => [])
   (OperandSwap.swap_fields (.formula a) (.formula ab) none (TypedContext.stack (.context Γ :: src)) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_swap] at h3
 have l3 : TM2.Reaches machine
   (config (.swap .done) none (TypedContext.stack (.formula a :: .formula ab :: .context Γ :: src)) [] (TypedContext.stack dst))
   (config (.pair (.copy (.scan (.run 2 .start)))) none (TypedContext.stack (.formula a :: .formula ab :: .context Γ :: src)) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run id Function.injective_id Control.pair ConjPremises.machine machine agree_pair (fun _ => [])
   (ConjPremises.construct Γ ab a none src dst) (by simp [config])
 simp only [embed_pair] at h4
 have l4 : TM2.Reaches machine
   (config (.pair .done) none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ a) ++ FramedRow.encode (.seq Γ ab) ++ TypedContext.stack dst))
   (config .done none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ a) ++ FramedRow.encode (.seq Γ ab) ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,orig,ab,Peirce.field,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans l4))))))))

end RosserDirect.ImpElimPremises
