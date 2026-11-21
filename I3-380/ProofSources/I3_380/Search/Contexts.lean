module
public import I3_380.Search.TermReader
@[expose] public section

namespace PalomarI3380

/-- The portions of the Polish word before and after the hole. -/
def RawContext.parts : RawContext → List Token × List Token
  | .hole => ([], [])
  | .app tag before nested after =>
    let (pre, post) := nested.parts
    (⟨before.length + 1 + after.length, tag⟩ :: (before.flatMap RawTerm.tokens ++ pre),
      post ++ after.flatMap RawTerm.tokens)

theorem RawContext.tokens_fill (ctx : RawContext) (term : RawTerm) :
    (ctx.fill term).tokens = ctx.parts.1 ++ term.tokens ++ ctx.parts.2 := by
  induction ctx with
  | hole => simp only [RawContext.fill, RawContext.parts, List.nil_append, List.append_nil]
  | app tag before nested after ih =>
    simp only [RawContext.fill, RawContext.parts, RawTerm.tokens_app, List.flatMap_append,
      List.flatMap_cons, List.length_append, List.length_cons, List.cons_append,
      List.append_assoc, ih]
    have len : before.length + (after.length + 1) = before.length + 1 + after.length := by omega
    rw [len]

private theorem split_children (xs : List RawTerm) (i : Nat)
    (h : i < (xs.flatMap RawTerm.tokens).length) :
    ∃ left child right,
      xs = left ++ child :: right ∧ (left.flatMap RawTerm.tokens).length ≤ i ∧
        i - (left.flatMap RawTerm.tokens).length < child.tokens.length := by
  induction xs generalizing i with
  | nil => simp at h
  | cons first rest ih =>
    simp only [List.flatMap_cons, List.length_append] at h
    by_cases inside : i < first.tokens.length
    · exact ⟨[], first, rest, rfl, Nat.zero_le _, inside⟩
    · obtain ⟨left, child, right, eq, earlier, after⟩ :=
        ih (i - first.tokens.length) (by omega)
      refine ⟨first :: left, child, right, ?_, ?_, ?_⟩
      · exact congrArg (List.cons first) eq
      · simp only [List.flatMap_cons, List.length_append]
        omega
      · simp only [List.flatMap_cons, List.length_append]
        omega

/-- Every token boundary in a complete term starts a subtree. -/
theorem RawTerm.context_at (term : RawTerm) (i : Nat) (h : i < term.tokens.length) :
    ∃ (ctx : RawContext) (child : RawTerm), ctx.fill child = term ∧ ctx.parts.1.length = i := by
  suffices aux : ∀ (n : Nat) (t : RawTerm) (j : Nat), sizeOf t = n →
      j < t.tokens.length → ∃ (ctx : RawContext) (child : RawTerm),
        ctx.fill child = t ∧ ctx.parts.1.length = j by
    exact aux (sizeOf term) term i rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t j hSize hi
    cases j with
    | zero => exact ⟨.hole, t, rfl, rfl⟩
    | succ j =>
      cases t with
      | app tag children =>
        simp only [RawTerm.tokens_app, List.length_cons] at hi
        obtain ⟨before, child, after, eq, hLen, childIndex⟩ := split_children children j (by omega)
        have member : child ∈ children := by rw [eq]; simp
        have smaller : sizeOf child < n := by
          have hChild := List.sizeOf_lt_of_mem member
          rw [← hSize]
          simp only [RawTerm.app.sizeOf_spec]
          omega
        obtain ⟨ctx, nested, hFill, hParts⟩ :=
          ih (sizeOf child) smaller child (j - (before.flatMap RawTerm.tokens).length) rfl childIndex
        refine ⟨.app tag before ctx after, nested, ?_, ?_⟩
        · simp only [RawContext.fill, hFill, ← eq]
        · simp only [RawContext.parts, List.length_cons, List.length_append, hParts]
          omega

/-- If the verifier matched a complete term at a token boundary, the
matched term is the subtree at that boundary, with the same suffix. -/
theorem RawTerm.context_of_slice (term subtree : RawTerm) (before after : List Token)
    (h : term.tokens = before ++ subtree.tokens ++ after) :
    ∃ (ctx : RawContext), ctx.fill subtree = term ∧ ctx.parts = (before, after) := by
  have len : before.length < term.tokens.length := by
    cases subtree with
    | app tag children =>
      rw [h, RawTerm.tokens_app]
      simp only [List.length_append, List.length_cons]
      omega
  obtain ⟨ctx, child, hContext, hLength⟩ := term.context_at before.length len
  have eqWords := ctx.tokens_fill child
  rw [hContext, h] at eqWords
  simp only [List.append_assoc] at eqWords
  obtain ⟨hBefore, hRemaining⟩ := List.append_inj eqWords hLength.symm
  obtain ⟨hSub, hAfter⟩ := RawTerm.prefix_unique hRemaining
  exact ⟨ctx, by rw [hSub]; exact hContext, Prod.ext hBefore.symm hAfter.symm⟩

end PalomarI3380
