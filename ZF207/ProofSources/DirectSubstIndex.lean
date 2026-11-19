module
public import DirectTypedNatAddition
public import DirectShiftIndex
@[expose] public section
namespace RosserDirect.SubstIndex
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512
inductive Q where
 | copy (q : Grammar.CopyControl TypedBlock.Control) | swap (q : OperandSwap.Control)
 | compare (q : TypedNatCompare.Q)
 | dropEq (q : Grammar.DropControl TypedBlock.Control)
 | dropOther (o : Ordering) (q : Grammar.DropControl TypedBlock.Control)
 | sum (q : TypedNatAddition.Q) | returnSum (q : Grammar.CopyControl TypedBlock.Control)
 | pred (q : TypedNatUnary.Control BinaryPredecessor.Q)
 | unchanged (q : Grammar.CopyControl TypedBlock.Control)
 | dropT (q : Grammar.DropControl TypedBlock.Control)
 | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .copy .done => .goto (fun _ => .swap (.first (.scan (.run 0 .start))))
 | .copy q => Routine.relocate id Q.copy (TypedBlock.machine q)
 | .swap .done => .goto (fun _ => .compare .leftTag)
 | .swap q => Routine.relocate id Q.swap (OperandSwap.machine q)
 | .compare (.done .eq) => .goto (fun _ => .dropEq (.scan (.run 1 .start)))
 | .compare (.done o) => .goto (fun _ => .dropOther o (.scan (.run 1 .start)))
 | .compare q => Routine.relocate id Q.compare (TypedNatCompare.machine q)
 | .dropEq .done => .goto (fun _ => .sum (.first (.scan (.run 0 .start))))
 | .dropEq q => Routine.relocate id Q.dropEq (TypedBlock.dropMachine q)
 | .dropOther .gt .done => .goto (fun _ => .unchanged (.scan (.run 0 .start)))
 | .dropOther .lt .done => .goto (fun _ => .pred .start)
 | .dropOther .eq .done => .goto (fun _ => .reject)
 | .dropOther o q => Routine.relocate SelectSecond.swap (Q.dropOther o) (TypedBlock.dropMachine q)
 | .sum .done => .goto (fun _ => .returnSum (.scan (.run 0 .start)))
 | .sum q => Routine.relocate SelectSecond.swap Q.sum (TypedNatAddition.machine q)
 | .returnSum .done => .goto (fun _ => .done)
 | .returnSum q => Routine.relocate id Q.returnSum (TypedBlock.moveMachine q)
 | .pred .done => .goto (fun _ => .dropT (.scan (.run 0 .start)))
 | .pred q => Routine.relocate id Q.pred (TypedNatUnary.machine BinaryPredecessor.machine .borrow .done q)
 | .unchanged .done => .goto (fun _ => .dropT (.scan (.run 0 .start)))
 | .unchanged q => Routine.relocate id Q.unchanged (TypedBlock.moveMachine q)
 | .dropT .done => .load (fun _ => none) (.goto (fun _ => .done))
 | .dropT q => Routine.relocate id Q.dropT (TypedBlock.dropMachine q)
 | .done | .reject => .halt

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

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Q.copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem agree_swap (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swap q) = Routine.relocate id Q.swap ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem agree_compare (q : TypedNatCompare.Q) (h : (TypedNatCompare.machine) q ≠ .halt) :
 machine (.compare q) = Routine.relocate id Q.compare ((TypedNatCompare.machine) q) := by
 cases q <;> simp_all [machine,TypedNatCompare.machine]

theorem agree_dropEq (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.dropEq q) = Routine.relocate id Q.dropEq ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem agree_sum (q : TypedNatAddition.Q) (h : (TypedNatAddition.machine) q ≠ .halt) :
 machine (.sum q) = Routine.relocate SelectSecond.swap Q.sum ((TypedNatAddition.machine) q) := by
 cases q <;> simp_all [machine,TypedNatAddition.machine]

theorem agree_returnSum (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.returnSum q) = Routine.relocate id Q.returnSum ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem agree_pred (q : TypedNatUnary.Control BinaryPredecessor.Q) (h : (TypedNatUnary.machine BinaryPredecessor.machine .borrow .done) q ≠ .halt) :
 machine (.pred q) = Routine.relocate id Q.pred ((TypedNatUnary.machine BinaryPredecessor.machine .borrow .done) q) := by
 cases q <;> simp_all [machine,TypedNatUnary.machine]

theorem agree_unchanged (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.unchanged q) = Routine.relocate id Q.unchanged ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem agree_dropT (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.dropT q) = Routine.relocate id Q.dropT ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem agree_dropOther (o : Ordering) (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.dropOther o q) = Routine.relocate SelectSecond.swap (Q.dropOther o) (TypedBlock.dropMachine q) := by
 cases q <;> cases o <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

abbrev field (n : Nat) := TypedContext.value (.nat n)

theorem compare_prefix (t d i : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (field i ++ field d ++ field t ++ src) [] dst)
 (config (.compare (.done (BinaryCompare.order .eq d i))) none (field i ++ field t ++ src) [] (field d ++ field t ++ dst)) := by
 have h0 := Routine.lift_embedded_run id Function.injective_id Q.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 2 [.nat i,.nat d,.nat t] rfl v src dst) (by simp [config])
 simp only [embed_id] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none (field i ++ field d ++ field t ++ src) [] (field i ++ field d ++ field t ++ dst))
   (config (.swap (.first (.scan (.run 0 .start)))) none (field i ++ field d ++ field t ++ src) [] (field i ++ field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run id Function.injective_id Q.swap OperandSwap.machine machine agree_swap (fun _ => [])
   (OperandSwap.swap_fields (.nat d) (.nat i) none (field t ++ src) (field i ++ field d ++ field t ++ dst)) (by simp [config])
 simp only [embed_id] at h1
 have l1 : TM2.Reaches machine
   (config (.swap .done) none (field d ++ field i ++ field t ++ src) [] (field i ++ field d ++ field t ++ dst))
   (config (.compare .leftTag) none (field d ++ field i ++ field t ++ src) [] (field i ++ field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Q.compare TypedNatCompare.machine machine agree_compare (fun _ => [])
   (TypedNatCompare.compare_values d i none (field i ++ field t ++ src) [] (field d ++ field t ++ dst)) (by simp [config])
 simp only [embed_id] at h2
 simp only [TM2.Reaches,field,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans h2)))

theorem discard_other (o : Ordering) (d t : Nat) (v : Option Symbol) (src dst : List Symbol) :
 ∃ w, TM2.Reaches machine
 (config (.dropOther o (.scan (.run 1 .start))) v src [] (field d ++ field t ++ dst))
 (config (.dropOther o .done) w src [] dst) := by
 obtain ⟨w,h⟩ := TypedBlock.drop_block 1 [.nat d,.nat t] rfl v dst [] src
 have h := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective (Q.dropOther o) TypedBlock.dropMachine machine (agree_dropOther o) (fun _ => []) h (by simp [config])
 exact ⟨w,by simpa [embed_swap,field,TypedContext.stack,List.append_assoc] using h⟩

theorem drop_t (t : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config (.dropT (.scan (.run 0 .start))) v (field t ++ src) [] dst)
 (config .done none src [] dst) := by
 obtain ⟨w,h⟩ := TypedBlock.drop_block 0 [.nat t] rfl v src [] dst
 have h := Routine.lift_embedded_run id Function.injective_id Q.dropT TypedBlock.dropMachine machine agree_dropT (fun _ => []) h (by simp [config])
 simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h
 have hl : TM2.Reaches machine (config (.dropT .done) w src [] dst) (config .done none src [] dst) := Relation.ReflTransGen.single rfl
 exact h.trans hl

theorem unchanged_run (i t : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config (.unchanged (.scan (.run 0 .start))) v (field i ++ field t ++ src) [] dst)
 (config .done none src [] (field i ++ dst)) := by
 have h := Routine.lift_embedded_run id Function.injective_id Q.unchanged TypedBlock.moveMachine machine agree_unchanged (fun _ => [])
   (TypedBlock.move_block 0 [.nat i] rfl v (field t ++ src) dst) (by simp [config])
 simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h
 have hl : TM2.Reaches machine (config (.unchanged .done) none (field t ++ src) [] (field i ++ dst))
   (config (.dropT (.scan (.run 0 .start))) none (field t ++ src) [] (field i ++ dst)) := Relation.ReflTransGen.single rfl
 simpa [TM2.Reaches,List.append_assoc] using h.trans (hl.trans (drop_t t none src (field i ++ dst)))

theorem pred_run (i t : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config (.pred .start) v (field i ++ field t ++ src) [] dst)
 (config .done none src [] (field (i-1) ++ dst)) := by
 have h := Routine.lift_embedded_run id Function.injective_id Q.pred (TypedNatUnary.machine BinaryPredecessor.machine .borrow .done) machine agree_pred (fun _ => [])
   (TypedNatUnary.predecessor i v (field t ++ src) dst) (by simp [config])
 simp only [embed_id] at h
 have hl : TM2.Reaches machine (config (.pred .done) none (field t ++ src) [] (field (i-1) ++ dst))
   (config (.dropT (.scan (.run 0 .start))) none (field t ++ src) [] (field (i-1) ++ dst)) := Relation.ReflTransGen.single rfl
 simpa [TM2.Reaches,List.append_assoc] using h.trans (hl.trans (drop_t t none src (field (i-1) ++ dst)))

theorem sum_run (t d : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config (.sum (.first (.scan (.run 0 .start)))) v src [] (field d ++ field t ++ dst))
 (config .done none src [] (field (t+d) ++ dst)) := by
 have h := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Q.sum TypedNatAddition.machine machine agree_sum (fun _ => [])
   (TypedNatAddition.addition t d v dst src) (by simp [config])
 simp only [embed_swap] at h
 have hl : TM2.Reaches machine (config (.sum .done) none (field (t+d) ++ src) [] dst)
   (config (.returnSum (.scan (.run 0 .start))) none (field (t+d) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have hm := Routine.lift_embedded_run id Function.injective_id Q.returnSum TypedBlock.moveMachine machine agree_returnSum (fun _ => [])
   (TypedBlock.move_block 0 [.nat (t+d)] rfl none src dst) (by simp [config])
 simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hm
 have he : TM2.Reaches machine (config (.returnSum .done) none src [] (field (t+d) ++ dst))
   (config .done none src [] (field (t+d) ++ dst)) := Relation.ReflTransGen.single rfl
 exact h.trans (hl.trans (hm.trans he))

/-- Finite binary de Bruijn substitution-index update. Consumes i,d,t and returns
if i<d then i, if i=d then t+d, otherwise i-1, preserving both raw tails. -/
theorem subst_index (t d i : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (field i ++ field d ++ field t ++ src) [] dst)
 (config .done none src [] (field (ZFR.sourceSubstIndex t d i) ++ dst)) := by
 have hp := compare_prefix t d i v src dst
 by_cases hlt : i < d
 · have ho : BinaryCompare.order .eq d i = .gt := by simp [BinaryCompare.order,hlt,show ¬d<i by omega]
   rw [ho] at hp
   have hl : TM2.Reaches machine (config (.compare (.done .gt)) none (field i ++ field t ++ src) [] (field d ++ field t ++ dst))
     (config (.dropOther .gt (.scan (.run 1 .start))) none (field i ++ field t ++ src) [] (field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
   obtain ⟨w,hd⟩ := discard_other .gt d t none (field i ++ field t ++ src) dst
   have he : TM2.Reaches machine (config (.dropOther .gt .done) w (field i ++ field t ++ src) [] dst)
     (config (.unchanged (.scan (.run 0 .start))) w (field i ++ field t ++ src) [] dst) := Relation.ReflTransGen.single rfl
   simpa [TM2.Reaches,ZFR.sourceSubstIndex,hlt] using hp.trans (hl.trans (hd.trans (he.trans (unchanged_run i t w src dst))))
 · by_cases heq : i = d
   · subst i
     have ho : BinaryCompare.order .eq d d = .eq := by simp [BinaryCompare.order]
     rw [ho] at hp
     have hl : TM2.Reaches machine (config (.compare (.done .eq)) none (field d ++ field t ++ src) [] (field d ++ field t ++ dst))
       (config (.dropEq (.scan (.run 1 .start))) none (field d ++ field t ++ src) [] (field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
     obtain ⟨w,h⟩ := TypedBlock.drop_block 1 [.nat d,.nat t] rfl none src [] (field d ++ field t ++ dst)
     have hd := Routine.lift_embedded_run id Function.injective_id Q.dropEq TypedBlock.dropMachine machine agree_dropEq (fun _ => []) h (by simp [config])
     simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at hd
     have he : TM2.Reaches machine (config (.dropEq .done) w src [] (field d ++ field t ++ dst))
       (config (.sum (.first (.scan (.run 0 .start)))) w src [] (field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
     have hs := sum_run t d w src dst
     simp only [TM2.Reaches,List.append_assoc] at hp hl hd he hs ⊢
     simpa [ZFR.sourceSubstIndex,field] using hp.trans (hl.trans (hd.trans (he.trans hs)))
   · have hgt : d < i := by omega
     have ho : BinaryCompare.order .eq d i = .lt := by simp [BinaryCompare.order,hgt]
     rw [ho] at hp
     have hl : TM2.Reaches machine (config (.compare (.done .lt)) none (field i ++ field t ++ src) [] (field d ++ field t ++ dst))
       (config (.dropOther .lt (.scan (.run 1 .start))) none (field i ++ field t ++ src) [] (field d ++ field t ++ dst)) := Relation.ReflTransGen.single rfl
     obtain ⟨w,hd⟩ := discard_other .lt d t none (field i ++ field t ++ src) dst
     have he : TM2.Reaches machine (config (.dropOther .lt .done) w (field i ++ field t ++ src) [] dst)
       (config (.pred .start) w (field i ++ field t ++ src) [] dst) := Relation.ReflTransGen.single rfl
     simpa [TM2.Reaches,ZFR.sourceSubstIndex,hlt,heq] using hp.trans (hl.trans (hd.trans (he.trans (pred_run i t w src dst))))

end RosserDirect.SubstIndex
