module
public import I3_334Support.Search.WordCompare
@[expose] public section

namespace PalomarI3380

/-- Compare the context prefix, consume the two instantiated sides,
and compare the untouched suffixes. -/
def acceptMatched (n old proposal : Nat) (lhs rhs : RawTerm) : Bool :=
  match comparePrefix n old proposal with
  | none => false
  | some (a, b) =>
    match matchTokens lhs.tokens a, matchTokens rhs.tokens b with
    | some left, some right => left == right
    | _, _ => false

theorem RawTerm.not_empty (t : RawTerm) : t.tokens ≠ [] := by
  cases t
  simp

theorem RawTerm.match_empty (t : RawTerm) : matchTokens t.tokens 0 = none := by
  cases t
  simp only [RawTerm.tokens_app, matchTokens_empty]

/-- Every accepted candidate replaces a genuine subtree. This includes
all arbitrary tags and all possible natural numbers proposed for the new word. -/
theorem acceptMatched_sound (n proposal : Nat) (old lhs rhs : RawTerm)
    (accepted : acceptMatched n (encodeTokens old.tokens 0) proposal lhs rhs = true) :
    ∃ ctx : RawContext,
      ctx.fill lhs = old ∧ encodeTokens (ctx.fill rhs).tokens 0 = proposal := by
  cases hPrefix : comparePrefix n (encodeTokens old.tokens 0) proposal with
  | none => simp [acceptMatched, hPrefix] at accepted
  | some remainder =>
    obtain ⟨a, b⟩ := remainder
    obtain ⟨hLeft, hRight⟩ := comparePrefix_incumbent old.tokens hPrefix
    cases hLhs : matchTokens lhs.tokens a with
    | none => simp [acceptMatched, hPrefix, hLhs] at accepted
    | some left =>
      cases hRhs : matchTokens rhs.tokens b with
      | none => simp [acceptMatched, hPrefix, hLhs, hRhs] at accepted
      | some right =>
        simp only [acceptMatched, hPrefix, hLhs, hRhs, beq_iff_eq] at accepted
        have hLe : n ≤ old.tokens.length := by
          by_cases hLe : n ≤ old.tokens.length
          · exact hLe
          · have hDrop : old.tokens.drop n = [] := List.drop_eq_nil_of_le (by omega)
            simp only [hLeft, hDrop, encodeTokens, RawTerm.match_empty] at hLhs
            contradiction
        have hLhsCopy := hLhs
        rw [hLeft] at hLhsCopy
        obtain ⟨suffix, hTail, hCode⟩ := matchTokens_incumbent (old.tokens.drop n) hLhsCopy
        have hOld : old.tokens = old.tokens.take n ++ lhs.tokens ++ suffix := by
          rw [List.append_assoc, ← hTail, List.take_append_drop]
        obtain ⟨ctx, hFill, hParts⟩ := old.context_of_slice lhs (old.tokens.take n) suffix hOld
        have hNew := matchTokens_sound hRhs
        refine ⟨ctx, hFill, ?_⟩
        rw [ctx.tokens_fill, hParts, List.append_assoc, encodeTokens_append, encodeTokens_append,
          ← hCode, accepted, hNew, ← hRight hLe]

/-- Every ground replacement fits the same numeric test. -/
theorem acceptMatched_complete (ctx : RawContext) (lhs rhs : RawTerm) :
    acceptMatched ctx.parts.1.length (encodeTokens (ctx.fill lhs).tokens 0)
      (encodeTokens (ctx.fill rhs).tokens 0) lhs rhs = true := by
  simp only [ctx.tokens_fill, List.append_assoc, encodeTokens_append, acceptMatched,
    comparePrefix_encoded, matchTokens_encoded, beq_self_eq_true]

end PalomarI3380
