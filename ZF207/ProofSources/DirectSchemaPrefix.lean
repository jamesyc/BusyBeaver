module
public import DirectFourStack
@[expose] public section
namespace RosserDirect.SchemaPrefix
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

def predMachine := ReturnValue.machine
 (TypedNatUnary.machine BinaryPredecessor.machine .borrow .done) .done
abbrev PredQ := ReturnValue.Q (TypedNatUnary.Control BinaryPredecessor.Q)

theorem decrement (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches predMachine
  (config (.first .start) v (TypedContext.value (.nat n) ++ src) [] dst)
  (config .done none (TypedContext.value (.nat (n-1)) ++ src) [] dst) := by
 simpa [predMachine] using ReturnValue.run
  (TypedNatUnary.machine BinaryPredecessor.machine .borrow .done) .done .start rfl
  (.nat (n-1)) v _ src dst (TypedNatUnary.predecessor n v src dst)

inductive Q where
 | prepare (q : ReverseTokens.Q) | check | pred (q : PredQ)
 | addBinder | reverse (q : ReverseTokens.Q) | finish | done | reject
 deriving DecidableEq, Fintype, Inhabited

def reverseRoles : Stack → K
 | .input => .stream | .scratch => .scratch | .output => .output

def machine : Q → Stmt4 Q
 | .prepare .done => .goto (fun _ => .check)
 | .prepare q => Routine.relocate prepareRoles Q.prepare (ReverseTokens.machine q)
 | .check => .pop .data (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
    (.peek .data (fun _ x => x)
     (.branch (fun x => x == some .tokenEnd)
      (.pop .data (fun _ x => x)
       (.pop .data (fun _ x => x)
        (.branch (fun x => x == some .frameEnd)
         (.goto (fun _ => .reverse .start)) (.goto (fun _ => .reject)))))
      (.push .data (fun _ => .tokenEnd) (.goto (fun _ => .pred (.first .start))))))
    (.goto (fun _ => .reject)))
 | .pred .done => .goto (fun _ => .addBinder)
 | .pred q => Routine.relocate dataRoles Q.pred (predMachine q)
 | .addBinder => .push .stream (fun _ => .tokenEnd)
   (.push .stream (fun _ => .bit1)
    (.push .stream (fun _ => .bit1)
     (.push .stream (fun _ => .bit0)
      (.push .stream (fun _ => .bit1) (.load (fun _ => none) (.goto (fun _ => .check)))))))
 | .reverse .done => .goto (fun _ => .finish)
 | .reverse q => Routine.relocate reverseRoles Q.reverse (ReverseTokens.machine q)
 | .finish => .push .output (fun _ => .tokenEnd)
   (.push .output (fun _ => .bit1) (.load (fun _ => none) (.goto (fun _ => .done))))
 | .done | .reject => .halt

theorem agree_prepare (q : ReverseTokens.Q) (h : ReverseTokens.machine q ≠ .halt) :
 machine (.prepare q) = Routine.relocate prepareRoles Q.prepare (ReverseTokens.machine q) := by
 cases q <;> simp_all [machine,ReverseTokens.machine]
theorem agree_pred (q : PredQ) (h : predMachine q ≠ .halt) :
 machine (.pred q) = Routine.relocate dataRoles Q.pred (predMachine q) := by
 cases q <;> simp_all [machine,predMachine,ReturnValue.machine]
theorem agree_reverse (q : ReverseTokens.Q) (h : ReverseTokens.machine q ≠ .halt) :
 machine (.reverse q) = Routine.relocate reverseRoles Q.reverse (ReverseTokens.machine q) := by
 cases q <;> simp_all [machine,ReverseTokens.machine]

theorem reverse_injective : Function.Injective reverseRoles := by
 intro a b h; cases a <;> cases b <;> simp_all [reverseRoles]
theorem embed_reverse (q : ReverseTokens.Q) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed reverseRoles Q.reverse (config q v p s c) (fun _ => a) =
 cfg4 (.reverse q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

def rev (f : ZFR.Formula) := payloadBits (ZFR.TokenVM.emitFormula f).reverse

theorem check_zero (v : Option Symbol) (p a c : List Symbol) :
 TM2.step machine (cfg4 .check v p (TypedContext.value (.nat 0) ++ a) [] c) =
 some (cfg4 (.reverse .start) (some .frameEnd) p a [] c) := by
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits,Nat.zero_bits,Function.update]
 funext k; cases k <;> rfl

theorem check_positive (n : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.step machine (cfg4 .check v p (TypedContext.value (.nat (n+1)) ++ a) [] c) =
 some (cfg4 (.pred (.first .start)) (some .bit0) p (TypedContext.value (.nat (n+1)) ++ a) [] c) := by
 have hb : (2*(n+1)).bits = false :: (n+1).bits := Nat.bit0_bits (n+1) (by omega)
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits,Nat.zero_bits,hb,bitSymbol,Function.update]

theorem add_binder (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.step machine (cfg4 .addBinder v (rev f ++ .frameEnd :: p) a [] c) =
 some (cfg4 .check none (rev (.all f) ++ .frameEnd :: p) a [] c) := by
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,rev,ZFR.TokenVM.emitFormula,
  List.reverse_append,payloadBits,tokenBits,bitSymbol,Function.update]
 funext k; cases k <;> rfl

theorem finish_step (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.step machine
  (cfg4 .finish v p a [] (payloadBits (ZFR.TokenVM.emitFormula f) ++ .frameEnd :: c)) =
 some (cfg4 .done none p a [] (TypedContext.value (.formula f) ++ c)) := by
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,valueSymbols,valueTokens,
  payloadBits,tokenBits,bitSymbol,Nat.one_bits,Function.update,List.append_assoc]
 funext k; cases k <;> rfl

theorem allPrefix_all (n : Nat) (f : ZFR.Formula) :
 ZFR.allPrefix n (.all f) = ZFR.allPrefix (n+1) f := by
 induction n with
 | zero => rfl
 | succ n ih => simpa [ZFR.allPrefix] using congrArg ZFR.Formula.all ih

/-- The counter is binary. Each iteration writes exactly one required binder,
and the formula payload is reversed only twice, not copied per binder. -/
theorem loop (n : Nat) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 .check v (rev f ++ .frameEnd :: p) (TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (ZFR.allPrefix n f)) ++ c)) := by
 induction n generalizing f v with
 | zero =>
  have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (check_zero v (rev f ++ .frameEnd :: p) a c)
  have h1 := Routine.lift_embedded_run reverseRoles reverse_injective Q.reverse
   ReverseTokens.machine machine agree_reverse (fun _ => a)
   (ReverseTokens.reverse_tokens (ZFR.TokenVM.emitFormula f).reverse (some .frameEnd) p c)
   (by simp [config])
  simp only [embed_reverse,List.reverse_reverse] at h1
  have h2 : TM2.Reaches machine
   (cfg4 (.reverse .done) none p a [] (payloadBits (ZFR.TokenVM.emitFormula f) ++ .frameEnd :: c))
   (cfg4 .finish none p a [] (payloadBits (ZFR.TokenVM.emitFormula f) ++ .frameEnd :: c)) := Relation.ReflTransGen.single rfl
  have h3 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (finish_step f none p a c)
  exact h0.trans (h1.trans (h2.trans h3))
 | succ n ih =>
  have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (check_positive n v (rev f ++ .frameEnd :: p) a c)
  have h1 := Routine.lift_embedded_run dataRoles data_injective Q.pred
   predMachine machine agree_pred (fun _ => rev f ++ .frameEnd :: p)
   (decrement (n+1) (some .bit0) a c) (by simp [config])
  simp only [embed_data,Nat.add_sub_cancel] at h1
  have h2 : TM2.Reaches machine
   (cfg4 (.pred .done) none (rev f ++ .frameEnd :: p) (TypedContext.value (.nat n) ++ a) [] c)
   (cfg4 .addBinder none (rev f ++ .frameEnd :: p) (TypedContext.value (.nat n) ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h3 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (add_binder f none p (TypedContext.value (.nat n) ++ a) c)
  have h4 := ih (.all f) none
  rw [allPrefix_all] at h4
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

/-- Construct allPrefix for arbitrary n and f, preserving all four tails. -/
theorem construct (n : Nat) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.prepare .formulaTag) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (ZFR.allPrefix n f)) ++ c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.prepare
  ReverseTokens.machine machine agree_prepare (fun _ => c)
  (ReverseTokens.reverse_formula f v (TypedContext.value (.nat n) ++ a) p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches machine
  (cfg4 (.prepare .done) none (rev f ++ .frameEnd :: p) (TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 .check none (rev f ++ .frameEnd :: p) (TypedContext.value (.nat n) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := loop n f none p a c
 simpa only [TM2.Reaches,List.append_assoc] using h0.trans (h1.trans h2)

end RosserDirect.SchemaPrefix
