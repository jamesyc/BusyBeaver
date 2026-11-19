module
public import DirectTypedNatCompare
public import NumericTransform
@[expose] public section
namespace RosserDirect.ShiftIndex
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512

inductive Q where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | swap (q : OperandSwap.Control)
 | compare (q : TypedNatCompare.Q)
 | drop (o : Ordering) (q : Grammar.DropControl TypedBlock.Control)
 | increment (q : TypedNatUnary.Control BinarySuccessor.Q)
 | unchanged (q : Grammar.CopyControl TypedBlock.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .copy .done => .goto (fun _ => .swap (.first (.scan (.run 0 .start))))
 | .copy q => Routine.relocate id Q.copy (TypedBlock.machine q)
 | .swap .done => .goto (fun _ => .compare .leftTag)
 | .swap q => Routine.relocate id Q.swap (OperandSwap.machine q)
 | .compare (.done o) => .goto (fun _ => .drop o (.scan (.run 0 .start)))
 | .compare q => Routine.relocate id Q.compare (TypedNatCompare.machine q)
 | .drop .gt .done => .goto (fun _ => .unchanged (.scan (.run 0 .start)))
 | .drop _ .done => .goto (fun _ => .increment .start)
 | .drop o q => Routine.relocate SelectSecond.swap (Q.drop o) (TypedBlock.dropMachine q)
 | .increment .done => .goto (fun _ => .done)
 | .increment q => Routine.relocate id Q.increment (TypedNatUnary.machine BinarySuccessor.machine .carry .done q)
 | .unchanged .done => .goto (fun _ => .done)
 | .unchanged q => Routine.relocate id Q.unchanged (TypedBlock.moveMachine q)
 | .done => .halt

theorem embed_id {L : Type} (labels : L → Q) (q : L) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id labels (config q v a b c) (fun _ => []) = config (labels q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_swap {L : Type} (labels : L → Q) (q : L) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap labels (config q v a b c) (fun _ => []) = config (labels q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Q.copy (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem agree_swap (q : OperandSwap.Control) (h : OperandSwap.machine q ≠ .halt) :
 machine (.swap q) = Routine.relocate id Q.swap (OperandSwap.machine q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]
theorem agree_compare (q : TypedNatCompare.Q) (h : TypedNatCompare.machine q ≠ .halt) :
 machine (.compare q) = Routine.relocate id Q.compare (TypedNatCompare.machine q) := by
 cases q <;> simp_all [machine,TypedNatCompare.machine]
theorem agree_drop (o : Ordering) (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.drop o q) = Routine.relocate SelectSecond.swap (Q.drop o) (TypedBlock.dropMachine q) := by
 cases q <;> cases o <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem agree_increment (q : TypedNatUnary.Control BinarySuccessor.Q)
 (h : TypedNatUnary.machine BinarySuccessor.machine .carry .done q ≠ .halt) :
 machine (.increment q) = Routine.relocate id Q.increment (TypedNatUnary.machine BinarySuccessor.machine .carry .done q) := by
 cases q <;> simp_all [machine,TypedNatUnary.machine]
theorem agree_unchanged (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.unchanged q) = Routine.relocate id Q.unchanged (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

/-- Finite-machine de Bruijn shift guard and index update. Input contains i,d,
output contains exactly (if i<d then i else i+1); no unbounded host computation. -/
theorem shift_index (d i : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
  (config (.copy (.scan (.run 1 .start))) v (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ src) [] dst)
  (config .done none src [] (TypedContext.value (.nat (ZFR.sourceShiftIndex d i)) ++ dst)) := by
 let o := BinaryCompare.order .eq d i
 have hc := Routine.lift_embedded_run id Function.injective_id Q.copy
   TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 1 [.nat i,.nat d] rfl v src dst) (by simp [config])
 simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hc
 have hc' : TM2.Reaches machine
   (config (.copy .done) none (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ src) [] (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ dst))
   (config (.swap (.first (.scan (.run 0 .start)))) none (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ src) [] (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ dst)) := Relation.ReflTransGen.single rfl
 have hs := Routine.lift_embedded_run id Function.injective_id Q.swap
   OperandSwap.machine machine agree_swap (fun _ => [])
   (OperandSwap.swap_fields (.nat d) (.nat i) none src (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ dst)) (by simp [config])
 simp only [embed_id] at hs
 have hs' : TM2.Reaches machine
   (config (.swap .done) none (TypedContext.value (.nat d) ++ TypedContext.value (.nat i) ++ src) [] (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ dst))
   (config (.compare .leftTag) none (TypedContext.value (.nat d) ++ TypedContext.value (.nat i) ++ src) [] (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ dst)) := Relation.ReflTransGen.single rfl
 have hp := Routine.lift_embedded_run id Function.injective_id Q.compare
   TypedNatCompare.machine machine agree_compare (fun _ => [])
   (TypedNatCompare.compare_values d i none (TypedContext.value (.nat i) ++ src) [] (TypedContext.value (.nat d) ++ dst)) (by simp [config])
 simp only [embed_id] at hp
 have hp' : TM2.Reaches machine
   (config (.compare (.done o)) none (TypedContext.value (.nat i) ++ src) [] (TypedContext.value (.nat d) ++ dst))
   (config (.drop o (.scan (.run 0 .start))) none (TypedContext.value (.nat i) ++ src) [] (TypedContext.value (.nat d) ++ dst)) := Relation.ReflTransGen.single rfl
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.nat d] rfl none dst [] (TypedContext.value (.nat i) ++ src)
 have hd := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective (Q.drop o)
   TypedBlock.dropMachine machine (agree_drop o) (fun _ => []) hw (by simp [config])
 simp only [embed_swap,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hd
 simp only [TM2.Reaches,List.append_assoc] at hc hc' hs hs' hp hp' hd ⊢
 have pref := hc.trans (hc'.trans (hs.trans (hs'.trans (hp.trans (hp'.trans hd)))))
 by_cases hi : i < d
 · have ho : o = .gt := by simp [o,BinaryCompare.order,hi,show ¬d<i by omega]
   rw [ho] at pref
   have hl : TM2.Reaches machine
     (config (.drop .gt .done) w (TypedContext.value (.nat i) ++ src) [] dst)
     (config (.unchanged (.scan (.run 0 .start))) w (TypedContext.value (.nat i) ++ src) [] dst) := Relation.ReflTransGen.single rfl
   have hu := Routine.lift_embedded_run id Function.injective_id Q.unchanged
     TypedBlock.moveMachine machine agree_unchanged (fun _ => [])
     (TypedBlock.move_block 0 [.nat i] rfl w src dst) (by simp [config])
   simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hu
   have hf : TM2.Reaches machine
     (config (.unchanged .done) none src [] (TypedContext.value (.nat i) ++ dst))
     (config .done none src [] (TypedContext.value (.nat i) ++ dst)) := Relation.ReflTransGen.single rfl
   simpa [ZFR.sourceShiftIndex,hi] using pref.trans (hl.trans (hu.trans hf))
 · have ho : o ≠ .gt := by simp [o,BinaryCompare.order,hi]; split <;> decide
   have hl : TM2.Reaches machine
     (config (.drop o .done) w (TypedContext.value (.nat i) ++ src) [] dst)
     (config (.increment .start) w (TypedContext.value (.nat i) ++ src) [] dst) := by
     apply Relation.ReflTransGen.single
     cases he : o with
     | lt => rfl
     | eq => rfl
     | gt => exact False.elim (ho he)
   have hu := Routine.lift_embedded_run id Function.injective_id Q.increment
     (TypedNatUnary.machine BinarySuccessor.machine .carry .done) machine agree_increment (fun _ => [])
     (TypedNatUnary.successor i w src dst) (by simp [config])
   simp only [embed_id] at hu
   have hf : TM2.Reaches machine
     (config (.increment .done) none src [] (TypedContext.value (.nat (i+1)) ++ dst))
     (config .done none src [] (TypedContext.value (.nat (i+1)) ++ dst)) := Relation.ReflTransGen.single rfl
   simpa [ZFR.sourceShiftIndex,hi] using pref.trans (hl.trans (hu.trans hf))

end RosserDirect.ShiftIndex
