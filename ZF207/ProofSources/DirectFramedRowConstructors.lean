module
public import DirectFramedRowEquality
@[expose] public section
namespace RosserDirect.FramedRowConstructor
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | formula0 (n : Fin 3) | formula1 (n : Fin 3)
 | scanFormula (n : Fin 3) | flushFormula (n : Fin 3)
 | context0 | context1 | context2 | entry | scan | flushContext | tag | done | reject
 deriving DecidableEq, Fintype, Inhabited

def afterFormula (n : Fin 3) : Control :=
 if h : n.val = 0 then .context0 else .formula0 ⟨n.val-1,by omega⟩

def machine (branches : Bool) : Control → Stmt Control
 | .formula0 n => TypedContext.expect .bit1 (.formula1 n) .reject
 | .formula1 n => TypedContext.expect .tokenEnd (.scanFormula n) .reject
 | .scanFormula n => scanStmt (.scanFormula n) (.flushFormula n) .reject [.frameEnd]
 | .flushFormula n => flushStmt (.flushFormula n) (afterFormula n)
 | .context0 => TypedContext.expect .bit0 .context1 .reject
 | .context1 => TypedContext.expect .bit1 .context2 .reject
 | .context2 => TypedContext.expect .tokenEnd .entry .reject
 | .entry => FramedContext.entryStmt .scan .flushContext .reject true
 | .scan => scanStmt .scan .entry .reject [.frameEnd]
 | .flushContext => flushStmt .flushContext .tag
 | .tag => .push .output (fun _ => if branches then .bit1 else .bit0) (.goto (fun _ => .done))
 | .done | .reject => .halt

theorem formula_tag (kind : Bool) (n : Fin 3) (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches (machine kind) (config (.formula0 n) v (tokenBits 1 ++ a) s c)
   (config (.scanFormula n) (some .tokenEnd) a s c) := by
 have h0 := TypedContext.expect_step (machine kind) (.formula0 n) (.formula1 n) .reject .bit1 rfl v (.tokenEnd :: a) s c
 have h1 := TypedContext.expect_step (machine kind) (.formula1 n) (.scanFormula n) .reject .tokenEnd rfl (some .bit1) a s c
 exact (TypedContext.reach_step h0).trans (TypedContext.reach_step h1)

theorem move_formula (kind : Bool) (n : Fin 3) (p : ZFR.Formula)
    (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine kind)
   (config (.formula0 n) v (TypedContext.value (.formula p) ++ src) [] dst)
   (config (afterFormula n) none src [] (FramedRow.formulaFrame p ++ dst)) := by
 have h0 := formula_tag kind n v (Membership.formulaPayload p ++ .frameEnd :: src) [] dst
 have h1 := Segment.transfer (machine kind) (.scanFormula n) (.flushFormula n) (afterFormula n) .reject [.frameEnd]
   rfl rfl (Membership.formulaPayload p) (payloadBits_no_end _) (some .tokenEnd) src dst
 simpa [TM2.Reaches, TypedContext.value, valueSymbols, valueTokens, payloadBits,
   Membership.formulaPayload, FramedRow.formulaFrame, List.append_assoc] using h0.trans h1

theorem context_tag (kind : Bool) (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches (machine kind) (config .context0 v (tokenBits 2 ++ a) s c)
   (config .entry (some .tokenEnd) a s c) := by
 have h0 := TypedContext.expect_step (machine kind) .context0 .context1 .reject .bit0 rfl v (.bit1 :: .tokenEnd :: a) s c
 have h1 := TypedContext.expect_step (machine kind) .context1 .context2 .reject .bit1 rfl (some .bit0) (.tokenEnd :: a) s c
 have h2 := TypedContext.expect_step (machine kind) .context2 .entry .reject .tokenEnd rfl (some .bit1) a s c
 exact (TypedContext.reach_step h0).trans ((TypedContext.reach_step h1).trans (TypedContext.reach_step h2))

theorem row_tag (kind : Bool) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step (machine kind) (config .tag v a s c) =
 some (config .done v a s ((if kind then .bit1 else .bit0) :: c)) := by
 cases kind <;> simp [machine, config, TM2.step, TM2.stepAux, storage]
 all_goals funext k; cases k <;> rfl

theorem finish_context (kind : Bool) (Γ : ZFR.Context)
    (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine kind)
   (config .context0 v (TypedContext.value (.context Γ) ++ src) [] dst)
   (config .done none src [] ((if kind then .bit1 else .bit0) :: (FramedContext.encode Γ ++ dst))) := by
 have h0 := context_tag kind v (FramedContext.encode Γ ++ src) [] dst
 have h1 := FramedContext.transfer_context (machine kind) .entry .scan .flushContext .tag .reject true
   rfl rfl rfl Γ (some .tokenEnd) src dst
 have h2 := TypedContext.reach_step (row_tag kind none src [] (Membership.contextFrames Γ ++ [.frameEnd] ++ dst))
 simp only [TM2.Reaches, List.append_assoc, ↓reduceIte] at h0 h1 h2
 simpa [TM2.Reaches, TypedContext.value, FramedContext.encode,List.append_assoc] using h0.trans (h1.trans h2)

/-- Exact sequent-row constructor from typed formula/context fields. -/
theorem construct_seq (Γ : ZFR.Context) (p : ZFR.Formula)
    (v : Option Symbol) (src : List ZFR.TokenVM.Value) (rows : List Symbol) :
 TM2.Reaches (machine false)
   (config (.formula0 0) v (TypedContext.stack (.formula p :: .context Γ :: src)) [] rows)
   (config .done none (TypedContext.stack src) [] (FramedRow.encode (.seq Γ p) ++ rows)) := by
 have h0 := move_formula false 0 p v (TypedContext.value (.context Γ) ++ TypedContext.stack src) rows
 have h1 := finish_context false Γ none (TypedContext.stack src) (FramedRow.formulaFrame p ++ rows)
 simpa [TM2.Reaches, afterFormula, TypedContext.stack, FramedRow.encode,List.append_assoc] using h0.trans h1

/-- Exact branch-pair row constructor. Input field order matches postfix VM:
last formula first, then prior formulas, then context. -/
theorem construct_branches (Γ : ZFR.Context) (p q r : ZFR.Formula)
    (v : Option Symbol) (src : List ZFR.TokenVM.Value) (rows : List Symbol) :
 TM2.Reaches (machine true)
   (config (.formula0 2) v (TypedContext.stack (.formula r :: .formula q :: .formula p :: .context Γ :: src)) [] rows)
   (config .done none (TypedContext.stack src) [] (FramedRow.encode (.branches Γ p q r) ++ rows)) := by
 have h0 := move_formula true 2 r v
   (TypedContext.value (.formula q) ++ TypedContext.value (.formula p) ++ TypedContext.value (.context Γ) ++ TypedContext.stack src) rows
 have h1 := move_formula true 1 q none
   (TypedContext.value (.formula p) ++ TypedContext.value (.context Γ) ++ TypedContext.stack src) (FramedRow.formulaFrame r ++ rows)
 have h2 := move_formula true 0 p none
   (TypedContext.value (.context Γ) ++ TypedContext.stack src) (FramedRow.formulaFrame q ++ (FramedRow.formulaFrame r ++ rows))
 have h3 := finish_context true Γ none (TypedContext.stack src)
   (FramedRow.formulaFrame p ++ (FramedRow.formulaFrame q ++ (FramedRow.formulaFrame r ++ rows)))
 simp only [TM2.Reaches, afterFormula, List.append_assoc] at h0 h1 h2 h3
 have h := h0.trans (h1.trans (h2.trans h3))
 simpa [TM2.Reaches, TypedContext.stack, FramedRow.encode,List.append_assoc] using h

end RosserDirect.FramedRowConstructor
