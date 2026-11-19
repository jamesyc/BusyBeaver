module
public import DirectNatPayload
@[expose] public section
namespace RosserDirect.AtomicFormula
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | tagB | scanB | flushB | tagA | scanA | flushA | tagOut | done | reject
 deriving DecidableEq, Fintype, Inhabited

def formula (equality : Bool) (a b : Nat) : ZFR.Formula := if equality then .eq a b else .mem a b

def machine (equality : Bool) : Control → Stmt Control
 | .tagB => TypedContext.expect .tokenEnd .scanB .reject
 | .scanB => scanStmt .scanB .flushB .reject (tokenBits (if equality then 5 else 3) ++ [.frameEnd])
 | .flushB => flushStmt .flushB .tagA
 | .tagA => TypedContext.expect .tokenEnd .scanA .reject
 | .scanA => scanStmt .scanA .flushA .reject []
 | .flushA => flushStmt .flushA .tagOut
 | .tagOut => .push .output (fun _ => .tokenEnd) (.push .output (fun _ => .bit1) (.goto (fun _ => .done)))
 | .done | .reject => .halt

theorem construct (kind : Bool) (a b : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine kind)
   (config .tagB v (TypedContext.value (.nat b) ++ TypedContext.value (.nat a) ++ src) [] dst)
   (config .done none src [] (TypedContext.value (.formula (formula kind a b)) ++ dst)) := by
 have h0 := TypedContext.reach_step (TypedContext.expect_step (machine kind) .tagB .scanB .reject .tokenEnd rfl v
   (tokenBits (2*b) ++ .frameEnd :: (TypedContext.value (.nat a) ++ src)) [] dst)
 have h1 := Segment.transfer (machine kind) .scanB .flushB .tagA .reject
   (tokenBits (if kind then 5 else 3) ++ [.frameEnd]) rfl rfl (tokenBits (2*b)) (tokenBits_no_end _) (some .tokenEnd)
   (TypedContext.value (.nat a) ++ src) dst
 have h2 := TypedContext.reach_step (TypedContext.expect_step (machine kind) .tagA .scanA .reject .tokenEnd rfl none
   (tokenBits (2*a) ++ .frameEnd :: src) []
   (tokenBits (2*b) ++ (tokenBits (if kind then 5 else 3) ++ [.frameEnd]) ++ dst))
 have h3 := Segment.transfer (machine kind) .scanA .flushA .tagOut .reject [] rfl rfl
   (tokenBits (2*a)) (tokenBits_no_end _) (some .tokenEnd) src
   (tokenBits (2*b) ++ (tokenBits (if kind then 5 else 3) ++ [.frameEnd]) ++ dst)
 have h4 : TM2.step (machine kind)
   (config .tagOut none src [] (tokenBits (2*a) ++ tokenBits (2*b) ++ tokenBits (if kind then 5 else 3) ++ .frameEnd :: dst)) =
   some (config .done none src []
     (.bit1 :: .tokenEnd :: (tokenBits (2*a) ++ tokenBits (2*b) ++ tokenBits (if kind then 5 else 3) ++ .frameEnd :: dst))) := by
   simp [machine,config,TM2.step,TM2.stepAux,storage]
   funext k; cases k <;> rfl
 have hz : tokenBits 0 = [.tokenEnd] := rfl
 simp only [TM2.Reaches,TypedContext.value,hz,List.append_assoc,List.singleton_append,List.append_nil,List.cons_append] at h0 h1 h2 h3 h4
 have h := h0.trans (h1.trans (h2.trans (h3.trans (TypedContext.reach_step h4))))
 have ht : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 cases kind <;> simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,formula,
   ZFR.TokenVM.emitFormula,ZFR.TokenVM.emitNat,payloadBits,List.flatMap_append,List.append_assoc,hz,ht] using h

end RosserDirect.AtomicFormula
