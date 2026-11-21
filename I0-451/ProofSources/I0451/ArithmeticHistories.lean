module
public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-! Internally finite histories for arithmetic-definable updates.
The construction uses a coded sequence and arithmetic induction. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure Iteration (step : V → V) (initial book length : V) : Prop where
  sequence : Seq book
  size : lh book = length + 1
  begins : znth book 0 = initial
  advances : ∀ j < length, znth book (j + 1) = step (znth book j)

theorem znth_append_old {book j : V} (seq : Seq book) (value : V) (inside : j < lh book) :
    znth (book ⁀' value) j = znth book j :=
  (seq.seqCons value).znth_eq_of_mem (Seq.mem_seqCons_iff_of_lt inside |>.mpr (seq.znth inside))

theorem znth_append_last {book : V} (seq : Seq book) (value : V) :
    znth (book ⁀' value) (lh book) = value :=
  (seq.seqCons value).znth_eq_of_mem (Seq.mem_seqCons book value)

theorem Iteration.singleton (step : V → V) (initial : V) :
    Iteration step initial (∅ ⁀' initial) 0 := by
  have empty : Seq (∅ : V) := seq_empty
  refine ⟨empty.seqCons _, by simp [empty.lh_seqCons], ?_, fun _ lt => (not_lt_zero lt).elim⟩
  simpa using znth_append_last empty initial

theorem Iteration.append {step : V → V} {initial book length : V}
    (ran : Iteration step initial book length) :
    Iteration step initial (book ⁀' step (znth book length)) (length + 1) := by
  let added := step (znth book length)
  have inside (j : V) (le : j ≤ length) : j < lh book := by rw [ran.size]; exact lt_succ_iff_le.mpr le
  refine ⟨ran.sequence.seqCons _, by rw [ran.sequence.lh_seqCons, ran.size], ?_, ?_⟩
  · rw [znth_append_old ran.sequence _ (inside _ (by simp))]
    exact ran.begins
  · intro j fits
    have le : j ≤ length := lt_succ_iff_le.mp fits
    rw [znth_append_old ran.sequence _ (inside _ le)]
    rcases eq_or_lt_of_le le with rfl | earlier
    · rw [← ran.size]
      exact znth_append_last ran.sequence added
    · rw [znth_append_old ran.sequence _ (inside _ (succ_le_iff_lt.mpr earlier))]
      exact ran.advances j earlier

theorem Iteration.append_value {step : V → V} {initial book length : V}
    (ran : Iteration step initial book length) :
    znth (book ⁀' step (znth book length)) (length + 1) = step (znth book length) := by
  rw [← ran.size]
  exact znth_append_last ran.sequence _

theorem iteration_defined (step : V → V) (defined : 𝚺ᴬ₁-Function₁[V] step) (initial : V) :
    𝚺ᴬ₁-Predicate[V] (fun length => ∃ book, Iteration step initial book length) := by
  have arithmetic : 𝚺ᴬ₁-Predicate[V] (fun len => ∃ book : V,
    Seq book ∧ lh book = len + 1 ∧ znth book 0 = initial ∧
      ∀ j < len, znth book (j + 1) = step (znth book j)) := by definability
  exact arithmetic.of_iff fun len => ⟨
    fun ⟨book, ran⟩ => ⟨book, ran.sequence, ran.size, ran.begins, ran.advances⟩,
    fun ⟨book, seq, size, first, steps⟩ => ⟨book, ⟨seq, size, first, steps⟩⟩⟩

theorem Iteration.exists (step : V → V) (defined : 𝚺ᴬ₁-Function₁[V] step) (initial length : V) :
    ∃ book, Iteration step initial book length := by
  induction length using ISigma1.sigma1_succ_induction with
  | zero => exact ⟨_, Iteration.singleton step initial⟩
  | succ k ih =>
    obtain ⟨book, ran⟩ := ih
    exact ⟨_, ran.append⟩
  | hP => exact iteration_defined step defined initial

theorem first_zero_at_most (book : V) (bound : V)
    (occurs : ∃ j ≤ bound, znth book j = 0) :
    ∃ j ≤ bound, znth book j = 0 ∧ ∀ i < j, znth book i ≠ 0 := by
  have first : ∀ bound : V, (∃ j ≤ bound, znth book j = 0) →
      ∃ j ≤ bound, znth book j = 0 ∧ ∀ i < j, znth book i ≠ 0 := by
    intro bound
    induction bound using ISigma1.sigma1_succ_induction with
    | zero =>
      rintro ⟨j, bound, zero⟩
      have same : j = 0 := le_antisymm bound (by simp)
      subst j
      exact ⟨0, le_refl _, zero, fun _ lt => (not_lt_zero lt).elim⟩
    | succ n ih =>
      intro existsZero
      by_cases before : ∃ j ≤ n, znth book j = 0
      · obtain ⟨j, bound, zero, noPrior⟩ := ih before
        exact ⟨j, bound.trans (by simp), zero, noPrior⟩
      · obtain ⟨j, bound, zero⟩ := existsZero
        have exactIndex : j = n + 1 := by
          rcases eq_or_lt_of_le bound with same | earlier
          · exact same
          · exact (before ⟨j, lt_succ_iff_le.mp earlier, zero⟩).elim
        refine ⟨n + 1, le_refl _, exactIndex ▸ zero, fun i lt early => ?_⟩
        exact before ⟨i, lt_succ_iff_le.mp lt, early⟩
    | hP => definability
  exact first bound occurs

/-- Track the first component when a paired state advances its clock by one. -/
theorem Iteration.clock {step : V → V} {initial book length : V}
    (ran : Iteration step initial book length) (first : π₁ initial = 0)
    (increment : ∀ state, π₁ (step state) = π₁ state + 1) :
    ∀ i ≤ length, π₁ (znth book i) = i := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | zero => intro _; rw [ran.begins, first]
  | succ i ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    rw [ran.advances i before, increment, ih (le_of_lt before)]
  | hP => definability

end I0451.Arithmetization
