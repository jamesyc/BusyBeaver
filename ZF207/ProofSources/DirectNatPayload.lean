module
public import DirectTypedContextConstructors
public import DirectEncodingInjective
@[expose] public section
namespace RosserDirect.NatPayload
open Turing
set_option backward.isDefEq.respectTransparency false

/-- Copy an arbitrarily long natural payload token, terminating at tokenEnd,
not frameEnd. The output gains a value-frame terminator. -/
def machine : Label → Statement
 | .scan => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
    (.push .scratch (fun _ => .tokenEnd)
     (.push .scratch (fun _ => .frameEnd) (.goto (fun _ => .flush))))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .scan)))
     (.goto (fun _ => .reject))))
 | .flush => RosserDirect.machine .flush
 | .done | .reject => .halt

theorem bit_step (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (cfg .scan v (bitSymbol b :: a) s out) =
 some (cfg .scan (some (bitSymbol b)) a (bitSymbol b :: s) out) := by
 cases b <;> simp [machine,bitSymbol,cfg,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem end_step (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (cfg .scan v (.tokenEnd :: a) s out) =
 some (cfg .flush (some .tokenEnd) a (.frameEnd :: .tokenEnd :: s) out) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem scan_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (cfg .scan v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   (cfg .flush (some .tokenEnd) a (.frameEnd :: .tokenEnd :: ((bs.map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (by rw [List.map_nil,List.nil_append,end_step]; rfl)
 | cons b bs ih =>
   have one : TM2.Reaches machine
     (cfg .scan v ((b :: bs).map bitSymbol ++ .tokenEnd :: a) s out)
     (cfg .scan (some (bitSymbol b)) (bs.map bitSymbol ++ .tokenEnd :: a) (bitSymbol b :: s) out) :=
     Relation.ReflTransGen.single (by rw [List.map_cons,List.cons_append,bit_step]; rfl)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some (bitSymbol b)) (bitSymbol b :: s))

theorem flush_all (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (cfg .flush v a s out) (cfg .done none a [] (s.reverse ++ out)) := by
 have h := Segment.flush_frame machine .flush .done rfl v a s out
 exact h

theorem nat_payload (n : Nat) (v : Option Symbol) (rest out : List Symbol) :
 TM2.Reaches machine (cfg .scan v (tokenBits n ++ rest) [] out)
   (cfg .done none rest [] (tokenBits n ++ .frameEnd :: out)) := by
 have h := (scan_bits n.bits v rest [] out).trans
   (flush_all (some .tokenEnd) rest (.frameEnd :: .tokenEnd :: ((n.bits.map bitSymbol).reverse ++ [])) out)
 simpa [TM2.Reaches,tokenBits,List.reverse_cons,List.append_assoc] using h

/-- Total specification decoder for the revised natural-value ABI. -/
def readNat (xs : List Symbol) : Option (Nat × List Symbol) := do
 let (tag,ys) := readTokenBits xs
 if tag.foldr Nat.bit 0 ≠ 0 then none else
 let (bits,rest) := readTokenBits ys
 let n := bits.foldr Nat.bit 0
 if n % 2 ≠ 0 then none else
 match rest with
 | .frameEnd :: tail => some (n/2,tail)
 | _ => none

end RosserDirect.NatPayload
