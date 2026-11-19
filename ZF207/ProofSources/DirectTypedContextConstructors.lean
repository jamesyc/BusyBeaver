module
public import DirectFramedContexts
@[expose] public section
namespace RosserDirect.TypedContext
open Turing Segment
set_option backward.isDefEq.respectTransparency false

/-- Revised runtime ABI, changing context storage and storing natural fields as their emitted2*n tokens. Other encodings
remain identical; certificates still carry the existing syntax representation. -/
def value : ZFR.TokenVM.Value → List Symbol
 | .context Γ => tokenBits 2 ++ FramedContext.encode Γ
 | .nat n => tokenBits 0 ++ tokenBits (2*n) ++ [.frameEnd]
 | v => valueSymbols v

def stack (vs : List ZFR.TokenVM.Value) : List Symbol := vs.flatMap value

inductive Control where
 | context0 | context1 | context2 | entry | scan | flushTail
 | formula0 | formula1 | scanHead | flushHead | tag | empty | done | reject
 deriving DecidableEq, Fintype, Inhabited

def expect {L : Type} (x : Symbol) (next fail : L) : Stmt L :=
 .pop .input (fun _ y => y)
  (.branch (fun y => y == some x) (.goto (fun _ => next)) (.goto (fun _ => fail)))

def tagOutput {L : Type} (next : L) : Stmt L :=
 .push .output (fun _ => .tokenEnd)
  (.push .output (fun _ => .bit1) (.push .output (fun _ => .bit0) (.goto (fun _ => next))))

/-- Typed context cons (VM opcode 9). Tags are checked by finite control,
not assumed or extracted by an unbounded host-language callback. -/
def machine : Control → Stmt Control
 | .context0 => expect .bit0 .context1 .reject
 | .context1 => expect .bit1 .context2 .reject
 | .context2 => expect .tokenEnd .entry .reject
 | .entry => FramedContext.entryStmt .scan .flushTail .reject true
 | .scan => scanStmt .scan .entry .reject [.frameEnd]
 | .flushTail => flushStmt .flushTail .formula0
 | .formula0 => expect .bit1 .formula1 .reject
 | .formula1 => expect .tokenEnd .scanHead .reject
 | .scanHead => scanStmt .scanHead .flushHead .reject [.frameEnd]
 | .flushHead => flushStmt .flushHead .tag
 | .tag => tagOutput .done
 | .empty => .push .output (fun _ => .frameEnd) (tagOutput .done)
 | .done | .reject => .halt

theorem expect_step {L : Type} (M : L → Stmt L) (q next fail : L) (x : Symbol)
    (hq : M q = expect x next fail) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step M (config q v (x :: a) s c) = some (config next (some x) a s c) := by
 cases x <;> simp [TM2.step, config, hq, expect, TM2.stepAux, storage, Function.update]
 all_goals funext k; cases k <;> rfl

theorem reach_step {L : Type} {M : L → Stmt L} {a b : Segment.Config L}
    (h : TM2.step M a = some b) : TM2.Reaches M a b :=
 Relation.ReflTransGen.single h

theorem context_tag (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (config .context0 v (tokenBits 2 ++ a) s c)
   (config .entry (some .tokenEnd) a s c) := by
 have h0 := expect_step machine .context0 .context1 .reject .bit0 rfl v (.bit1 :: .tokenEnd :: a) s c
 have h1 := expect_step machine .context1 .context2 .reject .bit1 rfl (some .bit0) (.tokenEnd :: a) s c
 have h2 := expect_step machine .context2 .entry .reject .tokenEnd rfl (some .bit1) a s c
 exact (reach_step h0).trans ((reach_step h1).trans (reach_step h2))

theorem formula_tag (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (config .formula0 v (tokenBits 1 ++ a) s c)
   (config .scanHead (some .tokenEnd) a s c) := by
 have h0 := expect_step machine .formula0 .formula1 .reject .bit1 rfl v (.tokenEnd :: a) s c
 have h1 := expect_step machine .formula1 .scanHead .reject .tokenEnd rfl (some .bit1) a s c
 exact (reach_step h0).trans (reach_step h1)

theorem output_tag (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (config .tag v a s c) =
 some (config .done v a s (tokenBits 2 ++ c)) := by
 simp [TM2.step, config, machine, tagOutput, TM2.stepAux, storage, tokenBits]
 funext k; cases k <;> rfl

theorem cons_payload (p : ZFR.Formula) (Γ : ZFR.Context)
    (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
   (config .context0 v
     ((tokenBits 2 ++ FramedContext.encode Γ) ++
      (tokenBits 1 ++ Membership.formulaPayload p ++ [.frameEnd]) ++ src) [] dst)
   (config .done none src [] ((tokenBits 2 ++ FramedContext.encode (p :: Γ)) ++ dst)) := by
 have h0 := context_tag v
   (FramedContext.encode Γ ++ tokenBits 1 ++ Membership.formulaPayload p ++ .frameEnd :: src) [] dst
 have h1 := FramedContext.transfer_context machine .entry .scan .flushTail .formula0 .reject true
   rfl rfl rfl Γ (some .tokenEnd)
   (tokenBits 1 ++ Membership.formulaPayload p ++ .frameEnd :: src) dst
 have h2 := formula_tag none (Membership.formulaPayload p ++ .frameEnd :: src) []
   (Membership.contextFrames Γ ++ [.frameEnd] ++ dst)
 have h3 := Segment.transfer machine .scanHead .flushHead .tag .reject [.frameEnd]
   rfl rfl (Membership.formulaPayload p) (payloadBits_no_end _) (some .tokenEnd) src
   (Membership.contextFrames Γ ++ [.frameEnd] ++ dst)
 have h4 : TM2.Reaches machine
   (config .tag none src []
    (Membership.formulaPayload p ++ [.frameEnd] ++ (Membership.contextFrames Γ ++ [.frameEnd] ++ dst)))
   (config .done none src []
    (tokenBits 2 ++ (Membership.formulaPayload p ++ [.frameEnd] ++ (Membership.contextFrames Γ ++ [.frameEnd] ++ dst)))) :=
   Relation.ReflTransGen.single (by rw [output_tag]; rfl)
 simp only [TM2.Reaches, List.append_assoc, ↓reduceIte] at h0 h1 h2 h3 h4
 have h := h0.trans (h1.trans (h2.trans (h3.trans h4)))
 simpa [TM2.Reaches, FramedContext.encode, Membership.contextFrames, Membership.frames,
   List.flatMap_cons, List.map_cons, List.append_assoc] using h

theorem cons_typed (p : ZFR.Formula) (Γ : ZFR.Context)
    (v : Option Symbol) (src dst : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (config .context0 v (stack (.context Γ :: .formula p :: src)) [] (stack dst))
   (config .done none (stack src) [] (stack (.context (p :: Γ) :: dst))) := by
 simpa [stack, value, valueSymbols, valueTokens, Membership.formulaPayload,
   payloadBits, List.append_assoc] using cons_payload p Γ v (stack src) (stack dst)

theorem empty_typed (v : Option Symbol) (src dst : List ZFR.TokenVM.Value) :
 TM2.step machine (config .empty v (stack src) [] (stack dst)) =
 some (config .done v (stack src) [] (stack (.context [] :: dst))) := by
 simp [machine, tagOutput, config, TM2.step, TM2.stepAux, stack, value,
   FramedContext.encode, Membership.contextFrames, Membership.frames, tokenBits, storage]
 funext k; cases k <;> rfl


end RosserDirect.TypedContext
