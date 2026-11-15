module
public import DirectContextMembership
public import DirectSegments
@[expose] public section
namespace RosserDirect.FramedContext
open Turing Segment
set_option backward.isDefEq.respectTransparency false

/-- Framed-list ABI: formula frames, then an empty frame as context terminator.
Real formula payloads are nonempty, so no formula can be mistaken for the end. -/
def encode (Γ : ZFR.Context) : List Symbol := Membership.contextFrames Γ ++ [.frameEnd]

theorem formula_nonempty (p : ZFR.Formula) : Membership.formulaPayload p ≠ [] := by
 intro h
 have he : ZFR.TokenVM.emitFormula p = [] := payloadBits_injective (by simpa [Membership.formulaPayload, payloadBits] using h)
 cases p <;> simp [ZFR.TokenVM.emitFormula] at he

def entryStmt {L : Type} (scan flush fail : L) (keepEnd : Bool) : Stmt L :=
 .pop .input (fun _ x => x)
  (.branch Option.isNone (.goto (fun _ => fail))
   (.branch (fun x => x == some .frameEnd)
    (if keepEnd then .push .scratch (fun _ => .frameEnd) (.goto (fun _ => flush))
      else .goto (fun _ => flush))
    (.push .scratch (fun x => x.getD .bit0) (.goto (fun _ => scan)))))

variable {L : Type} (M : L → Stmt L) (entry scan flush next fail : L) (keep : Bool)
variable (he : M entry = entryStmt scan flush fail keep)
variable (hs : M scan = scanStmt scan entry fail [.frameEnd])
variable (hf : M flush = flushStmt flush next)

include he in
theorem entry_symbol (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
    (a s out : List Symbol) :
 TM2.step M (config entry v (x :: a) s out) =
 some (config scan (some x) a (x :: s) out) := by
 cases x <;> cases keep <;> simp_all [TM2.step, config, he, entryStmt, TM2.stepAux, storage, Function.update]
 all_goals funext k; cases k <;> rfl

include he in
theorem entry_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step M (config entry v (.frameEnd :: a) s out) =
 some (config flush (some .frameEnd) a ((if keep then [.frameEnd] else []) ++ s) out) := by
 cases keep <;> simp [TM2.step, config, he, entryStmt, TM2.stepAux, storage, Function.update]
 all_goals funext k; cases k <;> rfl

include he hs in
theorem scan_context (Γ : ZFR.Context) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches M (config entry v (encode Γ ++ a) s out)
   (config flush (some .frameEnd) a
     ((if keep then [.frameEnd] else []) ++ (Membership.contextFrames Γ).reverse ++ s) out) := by
 induction Γ generalizing v s with
 | nil =>
   apply Relation.ReflTransGen.single
   simpa [encode, Membership.contextFrames, Membership.frames] using entry_end M entry scan flush fail keep he v a s out
 | cons p Γ ih =>
   have hn := formula_nonempty p
   obtain ⟨x,xs,hp⟩ : ∃ x xs, Membership.formulaPayload p = x :: xs := List.exists_cons_of_ne_nil hn
   have hv : ∀ y ∈ x :: xs, y ≠ .frameEnd := by rw [← hp]; exact payloadBits_no_end _
   have h0 : TM2.Reaches M
     (config entry v ((x :: xs) ++ .frameEnd :: (encode Γ ++ a)) s out)
     (config scan (some x) (xs ++ .frameEnd :: (encode Γ ++ a)) (x :: s) out) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, entry_symbol M entry scan flush fail keep he x (hv x (by simp))]; rfl)
   have h1 := Segment.scan_frame M scan entry fail [.frameEnd] hs xs
     (by intro y hy; exact hv y (by simp [hy])) (some x) (encode Γ ++ a) (x :: s) out
   have h2 := ih (some .frameEnd) ([.frameEnd].reverse ++ xs.reverse ++ x :: s)
   have h := h0.trans (h1.trans h2)
   simpa [TM2.Reaches, encode, Membership.contextFrames, Membership.frames,
     List.flatMap_cons, List.map_cons, hp, List.reverse_cons, List.reverse_append,
     List.append_assoc] using h

include he hs hf in
theorem transfer_context (Γ : ZFR.Context) (v : Option Symbol) (a out : List Symbol) :
 TM2.Reaches M (config entry v (encode Γ ++ a) [] out)
   (config next none a [] (Membership.contextFrames Γ ++ (if keep then [.frameEnd] else []) ++ out)) := by
 have h := (scan_context M entry scan flush fail keep he hs Γ v a [] out).trans
   (Segment.flush_frame M flush next hf (some .frameEnd) a
     ((if keep then [(Symbol.frameEnd)] else []) ++ (Membership.contextFrames Γ).reverse ++ []) out)
 cases keep <;> simpa [TM2.Reaches, List.reverse_append, List.append_assoc] using h

inductive Control where
 | entry | scan | flushTail | scanHead | flushHead | done | reject
 deriving DecidableEq, Fintype, Inhabited

/-- Cons constructor consumes tail-context then head-formula, matching the
original token VM argument order. Result has the framed-list ABI. -/
def constructor : Control → Stmt Control
 | .entry => entryStmt .scan .flushTail .reject true
 | .scan => scanStmt .scan .entry .reject [.frameEnd]
 | .flushTail => flushStmt .flushTail .scanHead
 | .scanHead => scanStmt .scanHead .flushHead .reject [.frameEnd]
 | .flushHead => flushStmt .flushHead .done
 | .done | .reject => .halt

/-- Preparation for membership: remove only the empty end-frame, preserving
all actual formula frame boundaries. The destination must be empty for lookup. -/
def prepare : Control → Stmt Control
 | .entry => entryStmt .scan .flushTail .reject false
 | .scan => scanStmt .scan .entry .reject [.frameEnd]
 | .flushTail => flushStmt .flushTail .done
 | _ => .halt

theorem prepare_membership (Γ : ZFR.Context) (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches prepare (config .entry v (encode Γ ++ src) [] [])
   (config .done none src [] (Membership.contextFrames Γ)) := by
 simpa using transfer_context prepare .entry .scan .flushTail .done .reject false
   rfl rfl rfl Γ v src []

def readFrame : List Symbol → List Symbol × List Symbol
 | [] => ([],[])
 | .frameEnd :: xs => ([],xs)
 | x :: xs => let (p,r) := readFrame xs; (x :: p,r)

theorem read_frame (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd) (rest : List Symbol) :
 readFrame (p ++ .frameEnd :: rest) = (p,rest) := by
 induction p with
 | nil => rfl
 | cons x xs ih =>
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [readFrame]

theorem read_encoded_cons (p : ZFR.Formula) (Γ : ZFR.Context) :
 readFrame (encode (p :: Γ)) = (Membership.formulaPayload p, encode Γ) := by
 simpa [encode, Membership.contextFrames, Membership.frames, List.append_assoc] using
   read_frame (Membership.formulaPayload p) (payloadBits_no_end _) (encode Γ)

theorem encode_injective : Function.Injective encode := by
 intro Γ
 induction Γ with
 | nil =>
   intro Δ h
   cases Δ with
   | nil => rfl
   | cons p Δ =>
     have hr := congrArg (fun s => (readFrame s).1) h
     rw [read_encoded_cons] at hr
     have hz : Membership.formulaPayload p = [] := hr.symm
     exact False.elim (formula_nonempty p hz)
 | cons p Γ ih =>
   intro Δ h
   cases Δ with
   | nil =>
     have hr := congrArg (fun s => (readFrame s).1) h
     rw [read_encoded_cons] at hr
     have hz : Membership.formulaPayload p = [] := hr
     exact False.elim (formula_nonempty p hz)
   | cons q Δ =>
     have hr := congrArg readFrame h
     rw [read_encoded_cons,read_encoded_cons] at hr
     exact congrArg₂ List.cons (Membership.formulaPayload_injective (congrArg Prod.fst hr))
       (ih (congrArg Prod.snd hr))

end RosserDirect.FramedContext
