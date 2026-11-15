module
public import DirectFourStack
@[expose] public section
namespace RosserDirect.FormulaPayloadCopy
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | tag0 | tag1 | scan | flush | finish | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .tag0 => TypedContext.expect .bit1 .tag1 .reject
 | .tag1 => TypedContext.expect .tokenEnd .scan .reject
 | .scan => .pop .input (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .reject))
    (.branch (fun x => x == some .frameEnd)
     (.push .input (fun _ => .frameEnd) (.goto (fun _ => .flush)))
     (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => .scan)))))
 | .flush => .pop .scratch (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .finish))
    (.push .input (fun x => x.getD .bit0)
     (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .flush)))))
 | .finish => .push .input (fun _ => .tokenEnd)
   (.push .input (fun _ => .bit1) (.load (fun _ => none) (.goto (fun _ => .done))))
 | .done | .reject => .halt

theorem scan_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config .scan v (x::a) s c) =
 some (config .scan (some x) a (x::s) c) := by
 cases x <;> simp_all [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_end (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config .scan v (.frameEnd::a) s c) =
 some (config .flush (some .frameEnd) (.frameEnd::a) s c) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem scan_payload (xs : List Symbol) (valid : ∀ x∈xs,x≠.frameEnd)
 (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (config .scan v (xs ++ .frameEnd::a) s c)
  (config .flush (some .frameEnd) (.frameEnd::a) (xs.reverse ++ s) c) := by
 induction xs generalizing v s with
 | nil => exact Relation.ReflTransGen.single (scan_end v a s c)
 | cons x xs ih =>
  have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (scan_step x (valid x (by simp)) v (xs ++ .frameEnd::a) s c)
  have h1 := ih (by intro y hy;exact valid y (by simp [hy])) (some x) (x::s)
  simpa only [TM2.Reaches,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append] using h0.trans h1

theorem flush_step (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config .flush v a (x::s) c) =
 some (config .flush (some x) (x::a) s (x::c)) := by
 cases x <;> simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem flush_payload (xs : List Symbol) (v : Option Symbol) (a c : List Symbol) :
 TM2.Reaches machine (config .flush v a xs c)
  (config .finish none (xs.reverse ++ a) [] (xs.reverse ++ c)) := by
 induction xs generalizing v a c with
 | nil =>
  apply Relation.ReflTransGen.single
  simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 | cons x xs ih =>
  have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (flush_step x v a xs c)
  have h1 := ih (some x) (x::a) (x::c)
  simpa only [TM2.Reaches,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append] using h0.trans h1

theorem copy_formula (f : ZFR.Formula) (v : Option Symbol) (a c : List Symbol) :
 TM2.Reaches machine
  (config .tag0 v (TypedContext.value (.formula f) ++ a) [] c)
  (config .done none (TypedContext.value (.formula f) ++ a) [] (payloadBits (ZFR.TokenVM.emitFormula f) ++ c)) := by
 let xs := payloadBits (ZFR.TokenVM.emitFormula f)
 have h0 : TM2.Reaches machine
  (config .tag0 v (.bit1::.tokenEnd::(xs ++ .frameEnd::a)) [] c)
  (config .tag1 (some .bit1) (.tokenEnd::(xs ++ .frameEnd::a)) [] c) :=
  Relation.ReflTransGen.single (TypedContext.expect_step machine .tag0 .tag1 .reject .bit1 rfl v _ [] c)
 have h1 : TM2.Reaches machine
  (config .tag1 (some .bit1) (.tokenEnd::(xs ++ .frameEnd::a)) [] c)
  (config .scan (some .tokenEnd) (xs ++ .frameEnd::a) [] c) :=
  Relation.ReflTransGen.single (TypedContext.expect_step machine .tag1 .scan .reject .tokenEnd rfl (some .bit1) _ [] c)
 have h2 := scan_payload xs (payloadBits_no_end _) (some .tokenEnd) a [] c
 have h3 := flush_payload xs.reverse (some .frameEnd) (.frameEnd::a) c
 simp only [List.append_nil,List.reverse_reverse] at h2 h3
 have h4 : TM2.Reaches machine
  (config .finish none (xs ++ .frameEnd::a) [] (xs ++ c))
  (config .done none (.bit1::.tokenEnd::(xs ++ .frameEnd::a)) [] (xs ++ c)) := by
  apply Relation.ReflTransGen.single
  simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
  funext k;cases k <;>rfl
 simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,payloadBits,tokenBits,bitSymbol,Nat.one_bits,List.append_assoc,xs] using
  h0.trans (h1.trans (h2.trans (h3.trans h4)))

end RosserDirect.FormulaPayloadCopy
