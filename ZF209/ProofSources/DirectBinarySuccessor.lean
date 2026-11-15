module
public import DirectNatPayload
@[expose] public section
namespace RosserDirect.BinarySuccessor
open Turing Segment
set_option backward.isDefEq.respectTransparency false

/-- Little-endian carry propagation; no conversion through unary naturals. -/
def inc : List Bool → List Bool
 | [] => [true]
 | false :: bs => true :: bs
 | true :: bs => false :: inc bs

theorem inc_bits (n : Nat) : inc n.bits = (n+1).bits := by
 induction n using Nat.binaryRec' with
 | zero => rfl
 | bit b n hn ih =>
   cases b with
   | false =>
     have hn' : n ≠ 0 := by intro h; exact Bool.noConfusion (hn h)
     rw [Nat.bits_append_bit n false hn,inc]
     exact (Nat.bit1_bits n).symm
   | true =>
     rw [Nat.bits_append_bit n true hn,inc,ih]
     have he : Nat.bit true n + 1 = 2*(n+1) := by simp [Nat.bit]; omega
     rw [he,Nat.bit0_bits (n+1) (by omega)]

inductive Q where
 | carry | copy | flush | done | reject
 deriving DecidableEq, Fintype, Repr, Inhabited

def machine : Q → Stmt Q
 | .carry => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .bit1)
    (.push .scratch (fun _ => .bit0) (.goto (fun _ => .carry)))
    (.branch (fun x => x == some .bit0)
     (.push .scratch (fun _ => .bit1) (.goto (fun _ => .copy)))
     (.branch (fun x => x == some .tokenEnd)
      (.push .scratch (fun _ => .bit1)
       (.push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush))))
      (.goto (fun _ => .reject)))))
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

theorem carry_one (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .carry v (.bit1 :: a) s out) =
 some (config .carry (some .bit1) a (.bit0 :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem carry_zero (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .carry v (.bit0 :: a) s out) =
 some (config .copy (some .bit0) a (.bit1 :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem carry_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .carry v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: .bit1 :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem carry_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .carry v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config .flush (some .tokenEnd) a (.tokenEnd :: (((inc bs).map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (carry_end v a s out)
 | cons b bs ih =>
   cases b with
   | false =>
     have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (carry_zero v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
     exact one.trans (by simpa [TM2.Reaches,inc,bitSymbol,List.reverse_cons,List.append_assoc] using copy_bits bs (some .bit0) a (.bit1 :: s) out)
   | true =>
     have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (carry_one v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
     exact one.trans (by simpa [TM2.Reaches,inc,bitSymbol,List.reverse_cons,List.append_assoc] using ih (some .bit1) (.bit0 :: s))

theorem successor (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .carry v (tokenBits n ++ src) [] dst)
  (config .done none src [] (tokenBits (n+1) ++ dst)) := by
 have h := (carry_bits n.bits v src [] dst).trans
   (Segment.flush_frame machine .flush .done rfl (some .tokenEnd) src
    (.tokenEnd :: (((inc n.bits).map bitSymbol).reverse ++ [])) dst)
 simpa [TM2.Reaches,tokenBits,inc_bits,List.reverse_cons,List.append_assoc] using h

end RosserDirect.BinarySuccessor
