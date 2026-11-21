module
public import I0451.ArithmeticHistories

/-! Concatenation of internally finite sequences. This operation
combines command words and proof records even in nonstandard models. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure AppendedPrefix (left right count result : V) : Prop where
  sequence : Seq result
  length : lh result = lh left + count
  first : ∀ i < lh left, znth result i = znth left i
  last : ∀ i < count, znth result (lh left + i) = znth right i

theorem AppendedPrefix.add {left right count result : V} (r : AppendedPrefix left right count result) :
    AppendedPrefix left right (count + 1) (result ⁀' znth right count) := by
  have len := r.sequence.lh_seqCons (znth right count)
  refine ⟨r.sequence.seqCons _, by rw [len, r.length, add_assoc], ?_, ?_⟩
  · intro i before
    have inside : i < lh result := by rw [r.length]; exact lt_of_lt_of_le before (by simp)
    rw [znth_append_old r.sequence _ inside]
    exact r.first i before
  · intro i before
    rcases eq_or_lt_of_le (lt_succ_iff_le.mp before) with rfl | old
    · rw [← r.length]
      exact znth_append_last r.sequence _
    · have inside : lh left + i < lh result := by
        rw [r.length, add_comm (lh left) i, add_comm (lh left) count]
        exact add_lt_add_left old _
      rw [znth_append_old r.sequence _ inside]
      exact r.last i old

private theorem appendedPrefix_exists_defined (left right : V) :
    𝚺ᴬ₁-Predicate[V] (fun count => ∃ result, AppendedPrefix left right count result) := by
  have described : 𝚺ᴬ₁-Predicate[V] (fun count => ∃ result : V,
      Seq result ∧ lh result = lh left + count ∧
        (∀ i < lh left, znth result i = znth left i) ∧
        (∀ i < count, znth result (lh left + i) = znth right i)) := by definability
  exact described.of_iff fun _ => ⟨
    fun ⟨result, h⟩ => ⟨result, h.sequence, h.length, h.first, h.last⟩,
    fun ⟨result, seq, len, first, last⟩ => ⟨result, ⟨seq, len, first, last⟩⟩⟩

theorem appendedPrefix_exists {left : V} (sequence : Seq left) (right count : V) :
    ∃ result, AppendedPrefix left right count result := by
  induction count using ISigma1.sigma1_succ_induction with
  | zero =>
    exact ⟨left, sequence, by simp, fun _ _ => rfl, fun _ lt => (not_lt_zero lt).elim⟩
  | succ n ih =>
    obtain ⟨result, prior⟩ := ih
    exact ⟨_, prior.add⟩
  | hP => exact appendedPrefix_exists_defined left right

theorem appendedSequence_exists {left : V} (sequence : Seq left) (right : V) :
    ∃ result, AppendedPrefix left right (lh right) result :=
  appendedPrefix_exists sequence right (lh right)

end I0451.Arithmetization
