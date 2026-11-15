module
public import DirectReverseTokens
@[expose] public section
namespace RosserDirect.NatUnframe
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | tag | scan | frame | flush | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .tag => TypedContext.expect .tokenEnd .scan .reject
 | .scan => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .frame))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .scan)))
     (.goto (fun _ => .reject))))
 | .frame => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
    (.push .input (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
    (.goto (fun _ => .reject)))
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .input (fun x => x.getD .bit0) (.goto (fun _ => .flush))))
 | .done | .reject => .halt

theorem scan_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .scan v (bitSymbol b :: a) s out) =
 some (config .scan (some (bitSymbol b)) a (bitSymbol b :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_token_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .scan v (.tokenEnd :: a) s out) =
 some (config .frame (some .tokenEnd) a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem scan_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .scan v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config .frame (some .tokenEnd) a ((bs.map bitSymbol).reverse ++ s) out) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (scan_token_end v a s out)
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (scan_bit b v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some (bitSymbol b)) (bitSymbol b :: s))

theorem frame_step (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .frame v (.frameEnd :: a) s out) =
 some (config .flush (some .frameEnd) (.tokenEnd :: a) s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem flush_bit (x : Symbol) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .flush v a (x :: s) out) =
 some (config .flush (some x) (x :: a) s out) := by
 cases x <;> simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem flush_empty (v : Option Symbol) (a out : List Symbol) :
 TM2.step machine (config .flush v a [] out) = some (config .done none a [] out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem flush_all (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .flush v a s out)
  (config .done none (s.reverse ++ a) [] out) := by
 induction s generalizing v a with
 | nil => exact Relation.ReflTransGen.single (flush_empty v a out)
 | cons x xs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (flush_bit x v a xs out)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some x) (x :: a))

/-- Remove the temporary type tag/frame without losing canonical binary token
bits. In-place on the input stack; output and arbitrary tails are untouched. -/
theorem unframe (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .tag v (TypedContext.value (.nat n) ++ src) [] dst)
  (config .done none (tokenBits (2*n) ++ src) [] dst) := by
 have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (TypedContext.expect_step machine .tag .scan .reject .tokenEnd rfl v (tokenBits (2*n) ++ .frameEnd :: src) [] dst)
 have h1 := scan_bits (2*n).bits (some .tokenEnd) (.frameEnd :: src) [] dst
 have h2 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (frame_step (some .tokenEnd) src (((2*n).bits.map bitSymbol).reverse ++ []) dst)
 have h3 := flush_all (some .frameEnd) (.tokenEnd :: src) (((2*n).bits.map bitSymbol).reverse ++ []) dst
 simp only [tokenBits,List.append_assoc,List.singleton_append] at h0
 simpa [TM2.Reaches,TypedContext.value,tokenBits,Nat.zero_bits,List.append_assoc] using h0.trans (h1.trans (h2.trans h3))

end RosserDirect.NatUnframe
