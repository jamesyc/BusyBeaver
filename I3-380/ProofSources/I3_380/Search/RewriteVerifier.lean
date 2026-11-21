module
public import I3_380.Search.Trial
public import I3_380.Rewriting
@[expose] public section

namespace PalomarI3380

def RawTerm.encode (t : RawTerm) : Nat := encodeTokens t.tokens 0

def singleConstant (c : Constant) : RawTerm := .app c.tag []

theorem rawCode_D : (singleConstant .D).encode = 4 := by
  rw [RawTerm.encode, singleConstant, RawTerm.tokens_app]
  rfl
theorem rawCode_J : (singleConstant .J).encode = 1 := by
  rw [RawTerm.encode, singleConstant, RawTerm.tokens_app]
  rfl

@[simp] theorem evaluate_singleConstant {A : Type} (M : Algebra A) (c : Constant) :
    (singleConstant c).evaluate M = M.constant c := by
  cases c <;> rw [singleConstant, RawTerm.evaluate_app] <;> rfl

def Term.variables {V : Type} : Term V → List V
  | .var i => [i]
  | .const _ => []
  | .neg x | .converse x | .choice x | .localRel x => x.variables
  | .nand x y | .product x y => x.variables ++ y.variables
  | .node x y z => x.variables ++ y.variables ++ z.variables

/-- Only dictionary coordinates used by the equation have to parse.
An unused entry has no effect on the instantiated sides. -/
def dictionaryTerm (dictionary : Fin 3 → Nat) (i : Fin 3) : RawTerm :=
  ((readTree (dictionary i)).map Prod.fst).getD (singleConstant .U)

def dictionaryValid (e : Equation) (dictionary : Fin 3 → Nat) : Bool :=
  (e.1.variables ++ e.2.variables).all fun i => (readTree (dictionary i)).isSome

def oriented (reverse : Bool) (e : Equation) : Equation :=
  if reverse then (e.2, e.1) else e

def verifyCandidate (e : Equation) (reverse : Bool) (position : Nat)
    (dictionary : Fin 3 → Nat) (old proposal : Nat) : Bool :=
  let selected := oriented reverse e
  dictionaryValid e dictionary &&
    acceptMatched position old proposal
      (selected.1.toRaw (dictionaryTerm dictionary)) (selected.2.toRaw (dictionaryTerm dictionary))

/-- A successful numeric match is a substitution instance under one
context. Every algebra satisfying the selected equation preserves its value. -/
theorem verifyCandidate_sound {e : Equation} {reverse : Bool} {position proposal : Nat}
    {dictionary : Fin 3 → Nat} (old : RawTerm)
    (h : verifyCandidate e reverse position dictionary old.encode proposal = true) :
    ∃ output : RawTerm, output.encode = proposal ∧
      ∀ (A : Type) (M : Algebra A), M.Satisfies e → output.evaluate M = old.evaluate M := by
  simp only [verifyCandidate, Bool.and_eq_true, RawTerm.encode] at h
  obtain ⟨ctx, hOld, hNew⟩ := acceptMatched_sound position proposal old _ _ h.2
  refine ⟨ctx.fill _, hNew, fun A M satisfies => ?_⟩
  rw [← hOld]
  apply RawContext.evaluate_eq
  have eq := satisfies (fun v => (dictionaryTerm dictionary v).evaluate M)
  simp only [Term.evaluate_toRaw]
  cases reverse
  · exact eq.symm
  · exact eq

theorem verifyCandidate_complete (e : Equation) (reverse : Bool) (ctx : RawContext)
    (σ : Fin 3 → RawTerm) :
    let selected := oriented reverse e
    verifyCandidate e reverse ctx.parts.1.length (fun i => (σ i).encode)
      (ctx.fill (selected.1.toRaw σ)).encode (ctx.fill (selected.2.toRaw σ)).encode = true := by
  have hRead (i : Fin 3) : readTree (σ i).encode = some (σ i, 0) :=
    readTree_complete (σ i) 0
  have valid : dictionaryValid e (fun i => (σ i).encode) = true := by
    unfold dictionaryValid
    apply List.all_eq_true.mpr
    intro i _
    simp only [hRead, Option.isSome_some]
  have dictionaryEq : dictionaryTerm (fun i => (σ i).encode) = σ := by
    funext i
    simp only [dictionaryTerm, hRead, Option.map_some, Option.getD_some]
  simp only [verifyCandidate]
  rw [valid, Bool.true_and, dictionaryEq]
  exact acceptMatched_complete ctx _ _

def ClosedTerm.raw (t : ClosedTerm) : RawTerm := t.toRaw Empty.elim

theorem Term.toRaw_subst {V W : Type} (σ : V → Term W) (τ : W → RawTerm) (t : Term V) :
    (t.subst σ).toRaw τ = t.toRaw (fun i => (σ i).toRaw τ) := by
  induction t <;> simp only [Term.subst, Term.toRaw, *]

def Frame.raw (f : Frame) : RawContext :=
  match f with
  | .neg => .app 0 [] .hole []
  | .converse => .app 3 [] .hole []
  | .choice => .app 1 [] .hole []
  | .localRel => .app 2 [] .hole []
  | .nandLeft y => .app 0 [] .hole [y.raw]
  | .nandRight x => .app 0 [x.raw] .hole []
  | .productLeft y => .app 1 [] .hole [y.raw]
  | .productRight x => .app 1 [x.raw] .hole []
  | .nodeFirst y z => .app 0 [] .hole [y.raw, z.raw]
  | .nodeSecond x z => .app 0 [x.raw] .hole [z.raw]
  | .nodeThird x y => .app 0 [x.raw, y.raw] .hole []

theorem Frame.raw_fill (f : Frame) (t : ClosedTerm) : (f.fill t).raw = f.raw.fill t.raw := by
  cases f <;> rfl

def RawContext.compose (outer inner : RawContext) : RawContext :=
  match outer with
  | .hole => inner
  | .app tag before nested after => .app tag before (nested.compose inner) after

theorem RawContext.compose_fill (outer inner : RawContext) (t : RawTerm) :
    (outer.compose inner).fill t = outer.fill (inner.fill t) := by
  induction outer <;> simp only [RawContext.compose, RawContext.fill, *]

theorem Replacement.numeric {E : List Equation} {s t : ClosedTerm} (h : Replacement E s t) :
    ∃ e ∈ E, ∃ reverse position dictionary,
      verifyCandidate e reverse position dictionary s.raw.encode t.raw.encode = true := by
  suffices shape : ∃ e ∈ E, ∃ (reverse : Bool) (ctx : RawContext) (σ : Fin 3 → RawTerm),
      s.raw = ctx.fill ((oriented reverse e).1.toRaw σ) ∧
        t.raw = ctx.fill ((oriented reverse e).2.toRaw σ) by
    obtain ⟨e, member, reverse, ctx, σ, left, right⟩ := shape
    exact ⟨e, member, reverse, ctx.parts.1.length, fun i => (σ i).encode,
      by rw [left, right]; exact verifyCandidate_complete e reverse ctx σ⟩
  induction h with
  | forward member σ =>
    exact ⟨_, member, false, .hole, fun i => (σ i).raw,
      Term.toRaw_subst σ _ _, Term.toRaw_subst σ _ _⟩
  | backward member σ =>
    exact ⟨_, member, true, .hole, fun i => (σ i).raw,
      Term.toRaw_subst σ _ _, Term.toRaw_subst σ _ _⟩
  | under f _ ih =>
    obtain ⟨e, member, reverse, ctx, σ, left, right⟩ := ih
    refine ⟨e, member, reverse, f.raw.compose ctx, σ, ?_, ?_⟩
    · rw [f.raw_fill, RawContext.compose_fill, left]
    · rw [f.raw_fill, RawContext.compose_fill, right]

/-- The integer words obtainable from the initial candidate by accepted
equational checks. Failed trials can only reset this search. -/
inductive NumericDerives (E : List Equation) : Nat → Prop where
  | start : NumericDerives E 4
  | next {e : Equation} {old new : Nat} {reverse : Bool} {position : Nat} {dict : Fin 3 → Nat} :
      NumericDerives E old → e ∈ E → verifyCandidate e reverse position dict old new = true →
      NumericDerives E new

theorem NumericDerives.sound {E : List Equation} {word : Nat} (h : NumericDerives E word) :
    ∃ t : RawTerm, t.encode = word ∧
      ∀ (A : Type) (M : Algebra A), M.Models E → t.evaluate M = M.constant .D := by
  induction h with
  | start => exact ⟨singleConstant .D, rawCode_D, fun _ M _ => evaluate_singleConstant M .D⟩
  | next _ member accepted ih =>
    obtain ⟨t, eq, value⟩ := ih
    rw [← eq] at accepted
    obtain ⟨output, code, preserves⟩ := verifyCandidate_sound t accepted
    exact ⟨output, code, fun A M hM => (preserves A M (hM _ member)).trans (value A M hM)⟩

theorem NumericDerives.of_chain {E : List Equation} {t : ClosedTerm}
    (h : RewriteChain E (.const .D) t) : NumericDerives E t.raw.encode := by
  induction h with
  | nil =>
    change NumericDerives E (singleConstant .D).encode
    rw [rawCode_D]
    exact .start
  | snoc _ next ih =>
    obtain ⟨e, member, _, _, _, check⟩ := next.numeric
    exact .next ih member check

/-- The numeric verifier accepts the halt word precisely when the
equational calculus has a derivation of the target equation. -/
theorem numeric_acceptance_iff :
    NumericDerives Manifest.final 1 ↔ Derives Manifest.final (.const .D) (.const .J) := by
  constructor
  · intro h
    obtain ⟨t, code, value⟩ := h.sound
    have eq : t = singleConstant .J := by
      have hCode : t.encode = (singleConstant .J).encode := code.trans rawCode_J.symm
      have hRead := congrArg readTree hCode
      simp only [RawTerm.encode, readTree_complete, Option.some.injEq, Prod.mk.injEq] at hRead
      exact hRead.1
    apply Derives.complete
    intro A M models
    have hEval := value A M models
    rw [eq, evaluate_singleConstant] at hEval
    exact hEval.symm
  · intro h
    rw [← rawCode_J]
    exact NumericDerives.of_chain h.rewriteChain

end PalomarI3380
