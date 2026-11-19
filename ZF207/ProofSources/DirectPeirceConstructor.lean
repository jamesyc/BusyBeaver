module
public import DirectOperandSwap
public import DirectBinaryConstructors
@[expose] public section
namespace RosserDirect.Peirce
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy0 (q : Grammar.CopyControl TypedBlock.Control)
 | imp0 (q : Binary.Control)
 | select0 (q : SelectSecond.Control)
 | copy1 (q : Grammar.CopyControl TypedBlock.Control)
 | swap0 (q : OperandSwap.Control)
 | imp1 (q : Binary.Control)
 | select1 (q : SelectSecond.Control)
 | swap1 (q : OperandSwap.Control)
 | imp2 (q : Binary.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy0 .done => .goto (fun _ => .imp0 .boot)
 | .copy0 q => Routine.relocate id Control.copy0 ((TypedBlock.machine) q)
 | .imp0 .done => .goto (fun _ => .select0 (.save .scan))
 | .imp0 q => Routine.relocate SelectSecond.swap Control.imp0 ((Binary.machine 11) q)
 | .select0 .done => .goto (fun _ => .copy1 (.scan (.run 1 .start)))
 | .select0 q => Routine.relocate id Control.select0 ((SelectSecond.machine) q)
 | .copy1 .done => .goto (fun _ => .swap0 (.first (.scan (.run 0 .start))))
 | .copy1 q => Routine.relocate id Control.copy1 ((TypedBlock.machine) q)
 | .swap0 .done => .goto (fun _ => .imp1 .boot)
 | .swap0 q => Routine.relocate SelectSecond.swap Control.swap0 ((OperandSwap.machine) q)
 | .imp1 .done => .goto (fun _ => .select1 (.save .scan))
 | .imp1 q => Routine.relocate SelectSecond.swap Control.imp1 ((Binary.machine 11) q)
 | .select1 .done => .goto (fun _ => .swap1 (.first (.scan (.run 0 .start))))
 | .select1 q => Routine.relocate id Control.select1 ((SelectSecond.machine) q)
 | .swap1 .done => .goto (fun _ => .imp2 .boot)
 | .swap1 q => Routine.relocate id Control.swap1 ((OperandSwap.machine) q)
 | .imp2 .done => .goto (fun _ => .done)
 | .imp2 q => Routine.relocate id Control.imp2 ((Binary.machine 11) q)
 | .done => .halt

theorem agree_copy0 (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy0 q) = Routine.relocate id Control.copy0 ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy0 (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy0 (config q v a b c) (fun _ => []) = config (.copy0 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_imp0 (q : Binary.Control) (h : (Binary.machine 11) q ≠ .halt) :
 machine (.imp0 q) = Routine.relocate SelectSecond.swap Control.imp0 ((Binary.machine 11) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_imp0 (q : Binary.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.imp0 (config q v a b c) (fun _ => []) = config (.imp0 q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_select0 (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.select0 q) = Routine.relocate id Control.select0 ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_select0 (q : SelectSecond.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.select0 (config q v a b c) (fun _ => []) = config (.select0 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_copy1 (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy1 q) = Routine.relocate id Control.copy1 ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy1 (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy1 (config q v a b c) (fun _ => []) = config (.copy1 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swap0 (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swap0 q) = Routine.relocate SelectSecond.swap Control.swap0 ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swap0 (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.swap0 (config q v a b c) (fun _ => []) = config (.swap0 q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_imp1 (q : Binary.Control) (h : (Binary.machine 11) q ≠ .halt) :
 machine (.imp1 q) = Routine.relocate SelectSecond.swap Control.imp1 ((Binary.machine 11) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_imp1 (q : Binary.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.imp1 (config q v a b c) (fun _ => []) = config (.imp1 q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_select1 (q : SelectSecond.Control) (h : (SelectSecond.machine) q ≠ .halt) :
 machine (.select1 q) = Routine.relocate id Control.select1 ((SelectSecond.machine) q) := by
 cases q <;> simp_all [machine,SelectSecond.machine]

theorem embed_select1 (q : SelectSecond.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.select1 (config q v a b c) (fun _ => []) = config (.select1 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swap1 (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swap1 q) = Routine.relocate id Control.swap1 ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swap1 (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.swap1 (config q v a b c) (fun _ => []) = config (.swap1 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_imp2 (q : Binary.Control) (h : (Binary.machine 11) q ≠ .halt) :
 machine (.imp2 q) = Routine.relocate id Control.imp2 ((Binary.machine 11) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_imp2 (q : Binary.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.imp2 (config q v a b c) (fun _ => []) = config (.imp2 q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev field (f : ZFR.Formula) := TypedContext.value (.formula f)

theorem imp_local (a b : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (Binary.machine 11)
 (config .boot v (field b ++ field a ++ src) [] dst)
 (config .done none src [] (field (.imp a b) ++ dst)) := by
 have h := Binary.assemble 11 (payloadBits (valueTokens (.formula a))) (Membership.formulaPayload b)
   (payloadBits_no_end _) (payloadBits_no_end _) v src dst
 have hb : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 simpa [field,TypedContext.value,valueSymbols,valueTokens,Membership.formulaPayload,
   ZFR.TokenVM.emitFormula,payloadBits,List.flatMap_append,List.append_assoc,hb] using h

/-- Finite constructor for the Peirce formula ((a → b) → a) → a.
All field sizes are unbounded and both surrounding stack tails are preserved. -/
theorem construct (a b : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.copy0 (.scan (.run 1 .start))) v (field b ++ field a ++ src) [] dst)
 (config .done none src [] (field (.imp (.imp (.imp a b) a) a) ++ dst)) := by
 let ab := ZFR.Formula.imp a b
 let mid := ZFR.Formula.imp ab a
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy0 TypedBlock.machine machine agree_copy0 (fun _ => [])
   (TypedBlock.copy_block 1 [.formula b,.formula a] rfl v src dst) (by simp [config])
 simp only [embed_copy0] at h0
 have l0 : TM2.Reaches machine
   (config (.copy0 .done) none (field b ++ field a ++ src) [] (field b ++ field a ++ dst))
   (config (.imp0 .boot) none (field b ++ field a ++ src) [] (field b ++ field a ++ dst)) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.imp0 (Binary.machine 11) machine agree_imp0 (fun _ => [])
   (imp_local a b none dst (field b ++ field a ++ src)) (by simp [config])
 simp only [embed_imp0] at h1
 have l1 : TM2.Reaches machine
   (config (.imp0 .done) none (field ab ++ field b ++ field a ++ src) [] dst)
   (config (.select0 (.save .scan)) none (field ab ++ field b ++ field a ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Control.select0 SelectSecond.machine machine agree_select0 (fun _ => [])
   (SelectSecond.select_second (.formula b) ab none (field a ++ src) dst) (by simp [config])
 simp only [embed_select0] at h2
 have l2 : TM2.Reaches machine
   (config (.select0 .done) none (field ab ++ field a ++ src) [] dst)
   (config (.copy1 (.scan (.run 1 .start))) none (field ab ++ field a ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.copy1 TypedBlock.machine machine agree_copy1 (fun _ => [])
   (TypedBlock.copy_block 1 [.formula ab,.formula a] rfl none src dst) (by simp [config])
 simp only [embed_copy1] at h3
 have l3 : TM2.Reaches machine
   (config (.copy1 .done) none (field ab ++ field a ++ src) [] (field ab ++ field a ++ dst))
   (config (.swap0 (.first (.scan (.run 0 .start)))) none (field ab ++ field a ++ src) [] (field ab ++ field a ++ dst)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.swap0 OperandSwap.machine machine agree_swap0 (fun _ => [])
   (OperandSwap.swap_fields (.formula a) (.formula ab) none dst (field ab ++ field a ++ src)) (by simp [config])
 simp only [embed_swap0] at h4
 have l4 : TM2.Reaches machine
   (config (.swap0 .done) none (field ab ++ field a ++ src) [] (field a ++ field ab ++ dst))
   (config (.imp1 .boot) none (field ab ++ field a ++ src) [] (field a ++ field ab ++ dst)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.imp1 (Binary.machine 11) machine agree_imp1 (fun _ => [])
   (imp_local ab a none dst (field ab ++ field a ++ src)) (by simp [config])
 simp only [embed_imp1] at h5
 have l5 : TM2.Reaches machine
   (config (.imp1 .done) none (field mid ++ field ab ++ field a ++ src) [] dst)
   (config (.select1 (.save .scan)) none (field mid ++ field ab ++ field a ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h6 := Routine.lift_embedded_run id Function.injective_id Control.select1 SelectSecond.machine machine agree_select1 (fun _ => [])
   (SelectSecond.select_second (.formula ab) mid none (field a ++ src) dst) (by simp [config])
 simp only [embed_select1] at h6
 have l6 : TM2.Reaches machine
   (config (.select1 .done) none (field mid ++ field a ++ src) [] dst)
   (config (.swap1 (.first (.scan (.run 0 .start)))) none (field mid ++ field a ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h7 := Routine.lift_embedded_run id Function.injective_id Control.swap1 OperandSwap.machine machine agree_swap1 (fun _ => [])
   (OperandSwap.swap_fields (.formula a) (.formula mid) none src dst) (by simp [config])
 simp only [embed_swap1] at h7
 have l7 : TM2.Reaches machine
   (config (.swap1 .done) none (field a ++ field mid ++ src) [] dst)
   (config (.imp2 .boot) none (field a ++ field mid ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h8 := Routine.lift_embedded_run id Function.injective_id Control.imp2 (Binary.machine 11) machine agree_imp2 (fun _ => [])
   (imp_local mid a none src dst) (by simp [config])
 simp only [embed_imp2] at h8
 have l8 : TM2.Reaches machine
   (config (.imp2 .done) none src [] (field (.imp mid a) ++ dst))
   (config .done none src [] (field (.imp mid a) ++ dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   field,List.append_assoc,ab,mid] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 h7 l7 h8 l8 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans (l6.trans (h7.trans (l7.trans (h8.trans l8))))))))))))))))

end RosserDirect.Peirce
