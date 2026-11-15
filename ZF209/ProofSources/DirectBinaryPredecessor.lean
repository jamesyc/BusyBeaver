module
public import DirectBinarySuccessor
@[expose] public section
namespace RosserDirect.BinaryPredecessor
open Turing Segment
set_option backward.isDefEq.respectTransparency false

/-- Binary borrow, removing the redundant most significant zero. -/
def dec : List Bool → List Bool
 | [] => []
 | false :: bs => true :: dec bs
 | true :: [] => []
 | true :: b :: bs => false :: b :: bs

theorem dec_bits (n : Nat) : dec n.bits = (n-1).bits := by
 induction n using Nat.binaryRec' with
 | zero => rfl
 | bit b n hn ih =>
   cases b with
   | false =>
     have hn' : n ≠ 0 := by intro h; exact Bool.noConfusion (hn h)
     rw [Nat.bits_append_bit n false hn,dec,ih]
     have he : Nat.bit false n - 1 = 2*(n-1)+1 := by simp [Nat.bit] <;> omega
     rw [he,Nat.bit1_bits]
   | true =>
     rw [Nat.bits_append_bit n true hn]
     by_cases hz : n = 0
     · subst n; rfl
     · have hbits : n.bits ≠ [] := by
         intro h
         have hf := fold_bits n
         rw [h] at hf
         exact hz hf.symm
       have he : Nat.bit true n - 1 = 2*n := by simp [Nat.bit] <;> omega
       rw [he,Nat.bit0_bits n hz]
       cases h : n.bits with
       | nil => exact False.elim (hbits h)
       | cons b bs => rfl

inductive Q where
 | borrow | afterOne | copy | flush | done | reject
 deriving DecidableEq, Fintype, Repr, Inhabited

def machine : Q → Stmt Q
 | .borrow => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .bit0)
    (.push .scratch (fun _ => .bit1) (.goto (fun _ => .borrow)))
    (.branch (fun x => x == some .bit1)
     (.goto (fun _ => .afterOne))
     (.branch (fun x => x == some .tokenEnd)
      (.push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
      (.goto (fun _ => .reject)))))
 | .afterOne => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
    (.push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun _ => .bit0)
      (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .copy))))
     (.goto (fun _ => .reject))))
 | .copy => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
    (.push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .copy)))
     (.goto (fun _ => .reject))))
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .flush))))
 | .done | .reject => .halt

theorem copy_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .copy v (bitSymbol b :: a) s out) =
 some (config .copy (some (bitSymbol b)) a (bitSymbol b :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem copy_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .copy v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem copy_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .copy v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config .flush (some .tokenEnd) a (.tokenEnd :: ((bs.map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (copy_end v a s out)
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (copy_bit b v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some (bitSymbol b)) (bitSymbol b :: s))

theorem borrow_one (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .borrow v (.bit1 :: a) s out) =
 some (config .afterOne (some .bit1) a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem borrow_zero (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .borrow v (.bit0 :: a) s out) =
 some (config .borrow (some .bit0) a (.bit1 :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem borrow_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .borrow v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem after_one_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .afterOne v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem after_one_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .afterOne v (bitSymbol b :: a) s out) =
 some (config .copy (some (bitSymbol b)) a (bitSymbol b :: .bit0 :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem borrow_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .borrow v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config .flush (some .tokenEnd) a (.tokenEnd :: (((dec bs).map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (borrow_end v a s out)
 | cons b bs ih =>
   cases b with
   | false =>
     have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (borrow_zero v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
     exact one.trans (by simpa [TM2.Reaches,dec,bitSymbol,List.reverse_cons,List.append_assoc] using ih (some .bit0) (.bit1 :: s))
   | true =>
     have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (borrow_one v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
     cases bs with
     | nil => exact one.trans (Relation.ReflTransGen.single (after_one_end (some .bit1) a s out))
     | cons b bs =>
       have two : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (after_one_bit b (some .bit1) (bs.map bitSymbol ++ .tokenEnd :: a) s out)
       exact one.trans (two.trans (by simpa [TM2.Reaches,dec,bitSymbol,List.reverse_cons,List.append_assoc] using copy_bits bs (some (bitSymbol b)) a (bitSymbol b :: .bit0 :: s) out))

theorem predecessor (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .borrow v (tokenBits n ++ src) [] dst)
  (config .done none src [] (tokenBits (n-1) ++ dst)) := by
 have h := (borrow_bits n.bits v src [] dst).trans
   (Segment.flush_frame machine .flush .done rfl (some .tokenEnd) src
    (.tokenEnd :: (((dec n.bits).map bitSymbol).reverse ++ [])) dst)
 simpa [TM2.Reaches,tokenBits,dec_bits,List.reverse_cons,List.append_assoc] using h

end RosserDirect.BinaryPredecessor
