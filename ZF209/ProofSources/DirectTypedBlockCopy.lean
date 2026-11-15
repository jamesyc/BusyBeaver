module
public import DirectGrammarCopy
public import Mathlib.Data.Fintype.Sigma
@[expose] public section
namespace RosserDirect.TypedBlock
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Phase where
 | start | tag0 | tag1 | expectOne | endPayload | endContext | payload | contextEntry | contextBody
 deriving DecidableEq, Fintype, Inhabited
inductive Control where
 | run (remaining : Fin 6) (phase : Phase) | done | reject
 deriving DecidableEq, Fintype, Inhabited

def active : Control → Prop | .run _ _ => True | _ => False
instance (q : Control) : Decidable (active q) := by cases q <;> unfold active <;> infer_instance

def finish (n : Fin 6) : Control :=
 if h : n.val = 0 then .done else .run ⟨n.val-1,by omega⟩ .start

def advance : Control → Symbol → Control
 | .run n .start, .tokenEnd => .run n .payload
 | .run n .start, .bit0 => .run n .tag0
 | .run n .start, .bit1 => .run n .tag1
 | .run n .tag0, .bit0 => .run n .expectOne
 | .run n .tag0, .bit1 => .run n .endContext
 | .run n .tag1, .tokenEnd => .run n .payload
 | .run n .tag1, .bit0 => .run n .expectOne
 | .run n .tag1, .bit1 => .run n .endPayload
 | .run n .expectOne, .bit1 => .run n .endPayload
 | .run n .endPayload, .tokenEnd => .run n .payload
 | .run n .endContext, .tokenEnd => .run n .contextEntry
 | .run n .payload, .frameEnd => finish n
 | .run n .payload, _ => .run n .payload
 | .run n .contextEntry, .frameEnd => finish n
 | .run n .contextEntry, _ => .run n .contextBody
 | .run n .contextBody, .frameEnd => .run n .contextEntry
 | .run n .contextBody, _ => .run n .contextBody
 | _, _ => .reject

abbrev Path := Grammar.Path active advance

def pathCheck : Control → List Symbol → Control → Bool
 | q, [], r => decide (q = r)
 | q, x :: xs, r => decide (active q) && pathCheck (advance q x) xs r

theorem check_sound (q r : Control) (p : List Symbol) (h : pathCheck q p r = true) : Path q p r := by
 induction p generalizing q with
 | nil => have he : q = r := of_decide_eq_true h; subst q; exact .nil _
 | cons x xs ih =>
   have hh : active q ∧ pathCheck (advance q x) xs r = true := by simpa [pathCheck] using h
   exact .cons hh.1 (ih _ hh.2)

theorem tags_checked : ∀ n tag : Fin 6, tag ≠ 2 →
 pathCheck (.run n .start) (tokenBits tag.val) (.run n .payload) = true := by decide

theorem context_tags_checked : ∀ n : Fin 6,
 pathCheck (.run n .start) (tokenBits 2) (.run n .contextEntry) = true := by decide

theorem tag_path (n tag : Fin 6) (h : tag ≠ 2) : Path (.run n .start) (tokenBits tag.val) (.run n .payload) :=
 check_sound _ _ _ (tags_checked n tag h)

theorem context_tag_path (n : Fin 6) : Path (.run n .start) (tokenBits 2) (.run n .contextEntry) :=
 check_sound _ _ _ (context_tags_checked n)

theorem payload_path (n : Fin 6) (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd) :
 Path (.run n .payload) (p ++ [.frameEnd]) (finish n) := by
 induction p with
 | nil => exact .cons trivial (.nil _)
 | cons x xs ih =>
   refine Grammar.Path.cons (q := Control.run n .payload) trivial ?_
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [advance]

theorem body_path (n : Fin 6) (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd) :
 Path (.run n .contextBody) (p ++ [.frameEnd]) (.run n .contextEntry) := by
 induction p with
 | nil => exact .cons trivial (.nil _)
 | cons x xs ih =>
   refine Grammar.Path.cons (q := Control.run n .contextBody) trivial ?_
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [advance]

theorem entry_formula_path (n : Fin 6) (p : ZFR.Formula) :
 Path (.run n .contextEntry) (FramedRow.formulaFrame p) (.run n .contextEntry) := by
 obtain ⟨x,xs,hp⟩ := List.exists_cons_of_ne_nil (FramedContext.formula_nonempty p)
 have hv : ∀ y ∈ x :: xs, y ≠ .frameEnd := by rw [← hp]; exact payloadBits_no_end _
 have hx := hv x (by simp)
 have hi := body_path n xs (by intro y hy; exact hv y (by simp [hy]))
 unfold FramedRow.formulaFrame
 rw [hp,List.cons_append]
 refine Grammar.Path.cons (q := Control.run n .contextEntry) trivial ?_
 cases x <;> simp_all [advance]

theorem context_path (n : Fin 6) (Γ : ZFR.Context) :
 Path (.run n .contextEntry) (FramedContext.encode Γ) (finish n) := by
 induction Γ with
 | nil => exact .cons trivial (.nil _)
 | cons p Γ ih =>
   simpa [FramedRow.formulaFrame,FramedContext.encode,Membership.contextFrames,Membership.frames,List.append_assoc] using
     (entry_formula_path n p).append ih

theorem value_path (n : Fin 6) (v : ZFR.TokenVM.Value) :
 Path (.run n .start) (TypedContext.value v) (finish n) := by
 cases v with
 | nat a => exact (tag_path n 0 (by decide)).append (payload_path n (tokenBits (2*a)) (tokenBits_no_end _))
 | formula p =>
   simpa [TypedContext.value,valueSymbols,valueTokens,payloadBits,List.append_assoc] using
     (tag_path n 1 (by decide)).append (payload_path n (payloadBits (ZFR.TokenVM.emitFormula p)) (payloadBits_no_end _))
 | context Γ => exact (context_tag_path n).append (context_path n Γ)
 | cert c =>
   simpa [TypedContext.value,valueSymbols,valueTokens,payloadBits,List.append_assoc] using
     (tag_path n 3 (by decide)).append (payload_path n (payloadBits (ZFR.TokenVM.emitCert c)) (payloadBits_no_end _))
 | witness w =>
   simpa [TypedContext.value,valueSymbols,valueTokens,payloadBits,List.append_assoc] using
     (tag_path n 4 (by decide)).append (payload_path n (payloadBits (ZFR.TokenVM.emitWitness w)) (payloadBits_no_end _))
 | witnesses ws =>
   simpa [TypedContext.value,valueSymbols,valueTokens,payloadBits,List.append_assoc] using
     (tag_path n 5 (by decide)).append (payload_path n (payloadBits (ZFR.TokenVM.emitWitnesses ws)) (payloadBits_no_end _))

/-- Up to six operand fields, each of arbitrary size and any VM type. Six is
only the finite-control arity limit, not a bound on formulas/contexts/naturals. -/
theorem block_path (n : Fin 6) (vs : List ZFR.TokenVM.Value) (len : vs.length = n.val+1) :
 Path (.run n .start) (TypedContext.stack vs) .done := by
 induction vs generalizing n with
 | nil => simp at len
 | cons v vs ih =>
   by_cases hn : n.val = 0
   · have hv : vs = [] := by apply List.eq_nil_of_length_eq_zero; simp at len; omega
     subst vs
     simpa [TypedContext.stack,finish,hn] using value_path n v
   · let k : Fin 6 := ⟨n.val-1,by omega⟩
     have hk : vs.length = k.val+1 := by simp at len; dsimp [k]; omega
     have h := (value_path n v).append (by simpa [finish,hn,k] using ih k hk)
     simpa [TypedContext.stack] using h

def machine := Grammar.copyMachine active advance Control.done

theorem copy_block (n : Fin 6) (vs : List ZFR.TokenVM.Value) (len : vs.length = n.val+1)
    (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
   (config (.scan (.run n .start)) v (TypedContext.stack vs ++ src) [] dst)
   (config .done none (TypedContext.stack vs ++ src) [] (TypedContext.stack vs ++ dst)) :=
 Grammar.copy_word active advance Control.done (by trivial) (block_path n vs len) v src dst

end RosserDirect.TypedBlock
