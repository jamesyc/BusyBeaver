module
public import I0451.Logic.SetSequences
public import I0451.Omega.ConcreteOmegaOrderArithmetic

/-! Concatenation of internally finite ordinal sequences, including
sequences whose entries are arbitrary sets in the model. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF207.OmegaInterpretation (add add_succ add_mem_omega)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure AppendedSetPrefix (left right count result : V) : Prop where
  sequence : Seq result
  length : lh result = add (lh left) count
  first : ∀ i ∈ lh left, znth result i = znth left i
  last : ∀ i ∈ count, znth result (add (lh left) i) = znth right i

private theorem add_extends (length count : V) (finite : count ∈ (ω : V)) : length ⊆ add length count := by
  apply naturalNumber_induction (fun n => length ⊆ add length n) _ _ _ count finite
  · definability
  · simpa only [ZF207.OmegaInterpretation.add_zero] using subset_refl length
  · intro n hn contained j hj
    rw [add_succ length n hn]
    exact mem_succ_iff.mpr (.inr (contained j hj))

theorem AppendedSetPrefix.extend {left right count result : V}
    (leftFinite : lh left ∈ (ω : V)) (countFinite : count ∈ (ω : V))
    (joined : AppendedSetPrefix left right count result) :
    AppendedSetPrefix left right (succ count) (result ⁀' znth right count) := by
  let value := znth right count
  have next := joined.sequence.seqCons value
  have old (i : V) (before : i ∈ lh result) : znth (result ⁀' value) i = znth result i :=
    next.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt before).mpr (joined.sequence.znth before))
  refine ⟨next, by rw [joined.sequence.lh_seqCons, joined.length, add_succ _ _ countFinite], ?_, ?_⟩
  · intro i inside
    have before : i ∈ lh result := joined.length.symm ▸ add_extends (lh left) count countFinite i inside
    rw [old i before]
    exact joined.first i inside
  · intro i included
    rcases mem_succ_iff.mp included with last | before
    · subst i
      rw [← joined.length]
      exact next.znth_eq_of_mem (Seq.mem_seqCons result value)
    · have natural := (show IsTransitive (ω : V) from inferInstance).transitive _ countFinite _ before
      have earlier : add (lh left) i ∈ lh result := by
        rw [joined.length]
        exact ZF207.OmegaInterpretation.add_lt_add_left i count (lh left) natural countFinite leftFinite before
      rw [old _ earlier]
      exact joined.last i before

private theorem appendedSetPrefix_exists_defined (left right : V) :
    ℒₛₑₜ-predicate (fun count => ∃ result, AppendedSetPrefix left right count result) := by
  have definition : ℒₛₑₜ-predicate (fun count => ∃ result : V, Seq result ∧ lh result = add (lh left) count ∧
      (∀ i ∈ lh left, znth result i = znth left i) ∧
      (∀ i ∈ count, znth result (add (lh left) i) = znth right i)) := by definability
  exact definition.of_iff fun _ => ⟨fun ⟨_, h⟩ => ⟨_, h.sequence, h.length, h.first, h.last⟩,
    fun ⟨_, sequence, length, first, last⟩ => ⟨_, ⟨sequence, length, first, last⟩⟩⟩

theorem appendedSetPrefix_exists {left : V} (sequence : Seq left) (short : lh left ∈ (ω : V))
    (right count : V) (finite : count ∈ (ω : V)) :
    ∃ result, AppendedSetPrefix left right count result := by
  apply naturalNumber_induction (fun n => ∃ result, AppendedSetPrefix left right n result)
    (appendedSetPrefix_exists_defined left right) _ _ count finite
  · exact ⟨left, sequence, (ZF207.OmegaInterpretation.add_zero _).symm, fun _ _ => rfl, fun i impossible => by
      simp [zero_def] at impossible⟩
  · intro n hn prior
    obtain ⟨result, joined⟩ := prior
    exact ⟨result ⁀' znth right n, joined.extend short hn⟩

theorem add_interval (left right : V) (finite : right ∈ (ω : V)) :
    ∀ i ∈ add left right, i ∈ left ∨ ∃ j ∈ right, i = add left j := by
  apply naturalNumber_induction (fun right => ∀ i ∈ add left right,
    i ∈ left ∨ ∃ j ∈ right, i = add left j) (by definability) _ _ right finite
  · intro i inside
    exact .inl (by simpa only [ZF207.OmegaInterpretation.add_zero] using inside)
  · intro r rNat prior i inside
    rw [add_succ left r rNat] at inside
    rcases mem_succ_iff.mp inside with latest | earlier
    · exact .inr ⟨r,mem_succ_self _,latest⟩
    · rcases prior i earlier with fst | ⟨j, previous, exactIndex⟩
      · exact .inl fst
      · exact .inr ⟨j,mem_succ_iff.mpr (.inr previous),exactIndex⟩

theorem AppendedSetPrefix.range {left right full : V} (joined : AppendedSetPrefix left right (lh right) full)
    (leftSeq : Seq left) (rightSeq : Seq right) (leftNat : lh left ∈ (ω : V)) (rightNat : lh right ∈ (ω : V)) :
    range full = range left ∪ range right := by
  apply mem_ext_iff.mpr
  intro x
  rw [mem_union_iff]
  constructor
  · intro appears
    obtain ⟨i, entry⟩ := mem_range_iff.mp appears
    have inside := joined.sequence.lt_lh_of_mem entry
    rw [joined.length] at inside
    have value := joined.sequence.znth_eq_of_mem entry
    rcases add_interval _ _ rightNat i inside with head | ⟨j, tail, rfl⟩
    · rw [joined.first i head] at value
      exact .inl (mem_range_iff.mpr ⟨i,value ▸ leftSeq.znth head⟩)
    · rw [joined.last j tail] at value
      exact .inr (mem_range_iff.mpr ⟨j,value ▸ rightSeq.znth tail⟩)
  · rintro (head | tail)
    · obtain ⟨i, entry⟩ := mem_range_iff.mp head
      have earlier := leftSeq.lt_lh_of_mem entry
      have within : i ∈ lh full := joined.length.symm ▸ add_extends _ _ rightNat i earlier
      have value := (joined.first i earlier).trans (leftSeq.znth_eq_of_mem entry)
      exact mem_range_iff.mpr ⟨i,value ▸ joined.sequence.znth within⟩
    · obtain ⟨i, entry⟩ := mem_range_iff.mp tail
      have earlier := rightSeq.lt_lh_of_mem entry
      have iNat := (show IsTransitive (ω : V) from inferInstance).transitive _ rightNat _ earlier
      have within : add (lh left) i ∈ lh full := joined.length.symm ▸
        ZF207.OmegaInterpretation.add_lt_add_left _ _ _ iNat rightNat leftNat earlier
      have value := (joined.last i earlier).trans (rightSeq.znth_eq_of_mem entry)
      exact mem_range_iff.mpr ⟨_,value ▸ joined.sequence.znth within⟩

end I0451.Logic.ZFModel
