module
public import DirectTypedNatCompare
@[expose] public section
namespace RosserDirect.ReverseTokens
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | formulaTag | formulaEnd | start | scan | flush | done | reject
 deriving DecidableEq, Fintype, Inhabited

/-- Reverse token order, not bit order. This makes postfix formula roots
available before their children while preserving the canonical binary ABI. -/
def machine : Q → Stmt Q
 | .formulaTag => TypedContext.expect .bit1 .formulaEnd .reject
 | .formulaEnd => TypedContext.expect .tokenEnd .start .reject
 | .start => .push .output (fun _ => .frameEnd) (.goto (fun _ => .scan))
 | .scan => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
    (.load (fun _ => none) (.goto (fun _ => .done)))
    (.branch (fun x => x == some .tokenEnd)
     (.push .output (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
     (.branch (fun x => x == some .bit0 || x == some .bit1)
      (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .scan)))
      (.goto (fun _ => .reject)))))
 | .flush => flushStmt .flush .scan
 | .done | .reject => .halt

theorem scan_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .scan v (bitSymbol b :: a) s out) =
 some (config .scan (some (bitSymbol b)) a (bitSymbol b :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_token_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .scan v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a s (.tokenEnd :: out)) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem scan_frame_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .scan v (.frameEnd :: a) s out) =
 some (config .done none a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem scan_bits (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .scan v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config .flush (some .tokenEnd) a ((bs.map bitSymbol).reverse ++ s) (.tokenEnd :: out)) := by
 induction bs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (scan_token_end v a s out)
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (scan_bit b v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   exact one.trans (by simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using ih (some (bitSymbol b)) (bitSymbol b :: s))

theorem token (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .scan v (tokenBits n ++ src) [] dst)
  (config .scan none src [] (tokenBits n ++ dst)) := by
 have hs := scan_bits n.bits v src [] dst
 have hf := Segment.flush_frame machine .flush .scan rfl (some .tokenEnd) src
   ((n.bits.map bitSymbol).reverse ++ []) (.tokenEnd :: dst)
 simpa [TM2.Reaches,tokenBits,List.append_assoc] using hs.trans hf

theorem tokens (ts : List Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .scan v (payloadBits ts ++ .frameEnd :: src) [] dst)
  (config .done none src [] (payloadBits ts.reverse ++ dst)) := by
 induction ts generalizing v dst with
 | nil => exact Relation.ReflTransGen.single (scan_frame_end v src [] dst)
 | cons n ts ih =>
   have h0 := token n v (payloadBits ts ++ .frameEnd :: src) dst
   have h1 := ih none (tokenBits n ++ dst)
   simpa [TM2.Reaches,payloadBits,List.flatMap_cons,List.reverse_cons,List.flatMap_append,List.append_assoc] using h0.trans h1

/-- Linear two-pass-per-token conversion; arbitrary token lengths and nesting. -/
theorem reverse_tokens (ts : List Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .start v (payloadBits ts ++ .frameEnd :: src) [] dst)
  (config .done none src [] (payloadBits ts.reverse ++ .frameEnd :: dst)) := by
 have h0 : TM2.Reaches machine
   (config .start v (payloadBits ts ++ .frameEnd :: src) [] dst)
   (config .scan v (payloadBits ts ++ .frameEnd :: src) [] (.frameEnd :: dst)) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
   funext k; cases k <;> rfl
 exact h0.trans (tokens ts v src (.frameEnd :: dst))

/-- Frontend-compatible temporary view of any canonical formula. The ordinary
stored formula ABI is unchanged; the output is an untagged root-first stream. -/
theorem reverse_formula (f : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .formulaTag v (TypedContext.value (.formula f) ++ src) [] dst)
  (config .done none src [] (payloadBits (ZFR.TokenVM.emitFormula f).reverse ++ .frameEnd :: dst)) := by
 have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (TypedContext.expect_step machine .formulaTag .formulaEnd .reject .bit1 rfl v
    (.tokenEnd :: (payloadBits (ZFR.TokenVM.emitFormula f) ++ .frameEnd :: src)) [] dst)
 have h1 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (TypedContext.expect_step machine .formulaEnd .start .reject .tokenEnd rfl (some .bit1)
    (payloadBits (ZFR.TokenVM.emitFormula f) ++ .frameEnd :: src) [] dst)
 have h2 := reverse_tokens (ZFR.TokenVM.emitFormula f) (some .tokenEnd) src dst
 simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,payloadBits,List.flatMap_cons,tokenBits,bitSymbol,Nat.one_bits,List.append_assoc] using h0.trans (h1.trans h2)

end RosserDirect.ReverseTokens
