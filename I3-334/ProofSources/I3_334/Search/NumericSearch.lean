module
public import I3_334.Search.DictionaryScan
public import I3_334.Proof.Ground
public import I3_334Support.Search.RewriteVerifier
public import Mathlib.Logic.Relation
@[expose] public section

namespace PalomarI3334

open PalomarI3380 Templates Relation

namespace Dictionary

def offset (slot : Fin 4) : Nat := if slot = 3 then 3 else 0

def coordinate (d : Dictionary) (slot : Fin 4) : Nat :=
  if slot = 0 then d.a else if slot = 1 then d.b else if slot = 2 then d.c else d.d

def capture (d : Dictionary) (slot : Fin 4) : RawTerm :=
  let tokens := (scanRaw (offset slot) (d.coordinate slot) 1).1
  ((readTree (encodeTokens tokens 0)).map Prod.fst).getD (.app (offset slot) [])

def ofTerms (terms : Fin 4 → RawTerm) : Dictionary :=
  let field (i : Fin 4) := writeRaw (offset i) (terms i).tokens 0
  ⟨field 0, field 1, field 2, field 3⟩

theorem capture_tokens (d : Dictionary) (slot : Fin 4) :
    (d.capture slot).tokens = (scanRaw (offset slot) (d.coordinate slot) 1).1 := by
  obtain ⟨trees, len, decoded, _⟩ := scanRaw_sound (offset slot) (d.coordinate slot) 1
  cases trees with
  | nil => contradiction
  | cons t tail =>
    have : tail = [] := by simpa using len
    subst tail
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at decoded
    simp only [capture, ← decoded, readTree_complete, Option.map_some, Option.getD_some]

theorem capture_guarded (d : Dictionary) : Guarded (d.capture 3) := by
  obtain ⟨trees, _, decoded, allowed⟩ := scanRaw_sound 3 d.d 1
  intro tok mem
  have seen : tok ∈ (scanRaw 3 d.d 1).1 := (capture_tokens d 3) ▸ mem
  exact allowed _ (decoded.symm ▸ seen)

/-- The R4/R5 fork inspects the unused suffix of slot a. Either branch
can be chosen while keeping the exact same substituted terms. -/
theorem capture_withTail (terms : Fin 4 → RawTerm) (safe : Guarded (terms 3)) (tail : Nat) :
    let d := { ofTerms terms with a := writeRaw 0 (terms 0).tokens tail }
    d.capture = terms ∧ (scanRaw 0 d.a 1).2 = tail := by
  let d := { ofTerms terms with a := writeRaw 0 (terms 0).tokens tail }
  have coords (i : Fin 4) : d.coordinate i =
      writeRaw (offset i) (terms i).tokens (if i = 0 then tail else 0) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have decoded (i : Fin 4) : scanRaw (offset i) (d.coordinate i) 1 =
      ((terms i).tokens, if i = 0 then tail else 0) := by
    have allowed tok (mem : tok ∈ (terms i).tokens) : offset i ≤ tok.tag := by
      unfold offset
      split
      · rename_i h
        subst i
        exact safe tok mem
      · omega
    rw [coords i]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
      List.length_nil] using scanRaw_writeRaw (offset i) [terms i] (if i = 0 then tail else 0)
        (by simpa using allowed)
  refine ⟨funext fun i => ?_, ?_⟩
  · change d.capture i = terms i
    simp only [capture, decoded, readTree_complete, Option.map_some, Option.getD_some]
  · simpa [offset, coordinate] using congrArg Prod.snd (decoded 0)

theorem capture_ofTerms (terms : Fin 4 → RawTerm) (safe : Guarded (terms 3)) :
    (ofTerms terms).capture = terms :=
  (capture_withTail terms safe 0).1

end Dictionary

def sides (eq : Templates.Equation) (reverse : Bool) : Templates.Equation :=
  if reverse then eq.swap else eq

/-- The numerical candidate test, with raw substitution words and canonical
biased arities in the incumbent and proposal. -/
def checkTrial (eq : Templates.Equation) (reverse : Bool) (position dictionary old next : Nat) : Bool :=
  let values := (Dictionary.decode dictionary).capture
  let chosen := sides eq reverse
  acceptMatched position old next (chosen.1.instantiate values) (chosen.2.instantiate values)

def NumericStep (old next : Nat) : Prop :=
  ∃ eq ∈ equations, ∃ reverse position dictionary, checkTrial eq reverse position dictionary old next = true

theorem numericStep_sound {next : Nat} (s : RawTerm) (step : NumericStep s.encode next) :
    ∃ t : RawTerm, t.encode = next ∧ Derives s t := by
  obtain ⟨eq, listed, reverse, position, dictionary, accepted⟩ := step
  let values := (Dictionary.decode dictionary).capture
  let chosen := sides eq reverse
  obtain ⟨ctx, current, output⟩ := acceptMatched_sound position next s
    (chosen.1.instantiate values) (chosen.2.instantiate values) accepted
  refine ⟨ctx.fill _, output, ?_⟩
  rw [← current]
  apply Derives.context
  have equality := Derives.instanceOf listed values (Dictionary.capture_guarded _)
  cases reverse
  · exact equality
  · exact equality.symm

def ContextStep (s t : RawTerm) : Prop :=
  ∃ eq ∈ equations, ∃ (reverse : Bool) (values : Fin 4 → RawTerm) (ctx : RawContext),
    Guarded (values 3) ∧ s = ctx.fill ((sides eq reverse).1.instantiate values) ∧
      t = ctx.fill ((sides eq reverse).2.instantiate values)

instance : Std.Symm ContextStep where
  symm _ _ h := by
    obtain ⟨eq, listed, dir, terms, ctx, safe, hs, ht⟩ := h
    refine ⟨eq, listed, !dir, terms, ctx, safe, ?_, ?_⟩ <;>
      cases dir <;> assumption

theorem ContextStep.under (ctx : RawContext) {s t : RawTerm} (h : ContextStep s t) :
    ContextStep (ctx.fill s) (ctx.fill t) := by
  obtain ⟨eq, listed, rev, σ, inner, safe, rfl, rfl⟩ := h
  exact ⟨eq, listed, rev, σ, ctx.compose inner, safe, (ctx.compose_fill _ _).symm,
    (ctx.compose_fill _ _).symm⟩

theorem Derives.chain {s t : RawTerm} (h : Derives s t) : ReflTransGen ContextStep s t := by
  induction h with
  | refl => exact .refl
  | symm _ ih => exact Std.Symm.symm _ _ ih
  | trans _ _ first second => exact first.trans second
  | instanceOf listed values safe => exact .single ⟨_, listed, false, values, .hole, safe, rfl, rfl⟩
  | context ctx _ ih => exact ih.lift ctx.fill (fun _ _ h => h.under ctx)

theorem ContextStep.numeric {s t : RawTerm} (h : ContextStep s t) :
    NumericStep s.encode t.encode := by
  obtain ⟨eq, listed, reverse, values, ctx, safe, rfl, rfl⟩ := h
  refine ⟨eq, listed, reverse, ctx.parts.1.length, (Dictionary.ofTerms values).encode, ?_⟩
  simp only [checkTrial, Dictionary.decode_encode, Dictionary.capture_ofTerms _ safe]
  apply acceptMatched_complete

private theorem numeric_chain_sound {s : RawTerm} {next : Nat}
    (h : ReflTransGen NumericStep s.encode next) :
    ∃ t : RawTerm, t.encode = next ∧ Derives s t := by
  induction h with
  | refl => exact ⟨s, rfl, .refl _⟩
  | tail _ step ih =>
    obtain ⟨t, rfl, h⟩ := ih
    obtain ⟨u, eq, known⟩ := numericStep_sound t step
    exact ⟨u, eq, h.trans known⟩

/-- An accepting chain of numerical trials exists exactly when the ten
guarded equations prove the target equation. -/
theorem numeric_acceptance_iff :
    ReflTransGen NumericStep 4 1 ↔ Derives (.app 1 []) (.app 0 []) := by
  have hd : (RawTerm.app 1 []).encode = 4 := by decide +kernel
  have hj : (RawTerm.app 0 []).encode = 1 := by decide +kernel
  rw [← hd, ← hj]
  constructor
  · intro h
    obtain ⟨t, eq, result⟩ := numeric_chain_sound h
    have same := congrArg readTree eq
    simp only [RawTerm.encode, readTree_complete, Option.some.injEq, Prod.mk.injEq, and_true] at same
    exact same ▸ result
  · intro h
    exact h.chain.lift RawTerm.encode (fun _ _ h => h.numeric)

end PalomarI3334
