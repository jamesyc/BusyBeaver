module
public import I0451.ArithmeticWordPrograms

/-! Composition of arithmetic command words. Both pieces may have
internally finite lengths. A zero proof-store code stays terminal. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem Iteration.word_value_succ {word history initial n i : V}
    (ran : Iteration (wordStep word) ⟪0, initial⟫ history n) (inWord : i < n) :
    π₂ (znth history (i + 1)) = barePacketStep (znth word i) (π₂ (znth history i)) := by
  simp only [ran.advances i inWord, wordStep, pi₂_pair, wordStep_index ran i (le_of_lt inWord)]

theorem WordRunsTo.zero (word : V) : WordRunsTo word 0 0 := by
  obtain ⟨trace, ran⟩ := Iteration.exists (wordStep word) (wordStep_defined word) ⟪0, 0⟫ (lh word)
  refine ⟨trace, ran, ?_⟩
  have stopped : ∀ i ≤ lh word, π₂ (znth trace i) = 0 := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | zero => intro _; simp [ran.begins]
    | succ i ih =>
      intro fits
      have prior := succ_le_iff_lt.mp fits
      rw [ran.word_value_succ prior, ih (le_of_lt prior)]
      simp [barePacketStep]
    | hP => definability
  exact stopped (lh word) (le_refl _)

private theorem word_prefix_matches {left right full start subtrace fulltrace : V}
    (joined : AppendedPrefix left right (lh right) full)
    (subrun : Iteration (wordStep left) ⟪0, start⟫ subtrace (lh left))
    (fullrun : Iteration (wordStep full) ⟪0, start⟫ fulltrace (lh full)) :
    ∀ j ≤ lh left, π₂ (znth fulltrace j) = π₂ (znth subtrace j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | zero => intro _; rw [subrun.begins, fullrun.begins]
  | succ j ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    have fullFits : j < lh full := by
      rw [joined.length]
      exact lt_of_lt_of_le before (by simp)
    rw [subrun.word_value_succ before, fullrun.word_value_succ fullFits, joined.first j before,
      ih (le_of_lt before)]
  | hP => definability

private theorem word_suffix_matches {left right full start middle fulltrace subtrace : V}
    (joined : AppendedPrefix left right (lh right) full)
    (fullrun : Iteration (wordStep full) ⟪0, start⟫ fulltrace (lh full))
    (subrun : Iteration (wordStep right) ⟪0, middle⟫ subtrace (lh right))
    (atStart : π₂ (znth fulltrace (lh left)) = middle) :
    ∀ j ≤ lh right, π₂ (znth fulltrace (lh left + j)) = π₂ (znth subtrace j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | zero =>
    intro _
    rw [subrun.begins, pi₂_pair, add_zero, atStart]
  | succ j ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    have fullFits : lh left + j < lh full := by
      rw [joined.length, add_comm (lh left) j, add_comm (lh left) (lh right)]
      exact add_lt_add_left before _
    rw [← add_assoc, subrun.word_value_succ before, fullrun.word_value_succ fullFits, joined.last j before,
      ih (le_of_lt before)]
  | hP => definability

theorem WordRunsTo.append {left right full start middle result : V}
    (before : WordRunsTo left start middle) (after : WordRunsTo right middle result)
    (joined : AppendedPrefix left right (lh right) full) :
    WordRunsTo full start result := by
  obtain ⟨first, leftRan, mid⟩ := before
  obtain ⟨last, rightRan, final⟩ := after
  obtain ⟨trace, whole⟩ := Iteration.exists (wordStep full) (wordStep_defined full) ⟪0, start⟫ (lh full)
  have firstPart := word_prefix_matches joined leftRan whole (lh left) (le_refl _)
  have remainder := word_suffix_matches joined whole rightRan (firstPart.trans mid) (lh right) (le_refl _)
  exact ⟨trace, whole, joined.length.symm ▸ remainder.trans final⟩

theorem WordRunsTo.unique {word initial a b : V} (left : WordRunsTo word initial a)
    (right : WordRunsTo word initial b) : a = b := by
  obtain ⟨x, first, hs⟩ := left
  obtain ⟨y, second, ht⟩ := right
  have agrees : ∀ i ≤ lh word, znth x i = znth y i := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | zero => intro _; rw [first.begins, second.begins]
    | succ i ih =>
      intro within
      have before := succ_le_iff_lt.mp within
      rw [first.advances i before, second.advances i before, ih (le_of_lt before)]
    | hP => definability
  rw [← hs, ← ht, agrees _ (le_refl _)]

end I0451.Arithmetization
