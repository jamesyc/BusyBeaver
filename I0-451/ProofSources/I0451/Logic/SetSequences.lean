module
public import Foundation.FirstOrder.SetTheory.Recursion.Seq
public import Foundation.FirstOrder.SetTheory.ZF.ZF

/-! An ordinal sequence of uniquely specified bounded values exists
by Separation. This is used for internal parameter tuples. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

theorem functionFromRelation {domain bound : V}
    {R : V → V → Prop} (defR : ℒₛₑₜ-relation R)
    (each : ∀ i ∈ domain, ∃! x, x ∈ bound ∧ R i x) :
    ∃ f ∈ bound ^ domain, ∀ i x, ⟨i,x⟩ₖ ∈ f ↔ i ∈ domain ∧ x ∈ bound ∧ R i x := by
  let contains (p : V) := ∃ i ∈ domain, ∃ x ∈ bound, p = ⟨i,x⟩ₖ ∧ R i x
  have hDef : ℒₛₑₜ-predicate contains := by unfold contains; definability
  let tuple := sep (domain ×ˢ bound) contains hDef
  have entry (i x : V) : ⟨i,x⟩ₖ ∈ tuple ↔ i ∈ domain ∧ x ∈ bound ∧ R i x := by
    constructor
    · intro h
      obtain ⟨_, j, hj, y, hy, eq, relation⟩ := mem_sep_iff.mp h
      obtain ⟨rfl, rfl⟩ := kpair_inj eq
      exact ⟨hj, hy, relation⟩
    · rintro ⟨inside, fits, relation⟩
      exact mem_sep_iff.mpr ⟨mem_prod_iff.mpr ⟨i, inside, x, fits, rfl⟩,
        ⟨i, inside, x, fits, rfl, relation⟩⟩
  have memFunction : tuple ∈ bound ^ domain := by
    apply mem_function.intro
    · exact fun p hp => (mem_sep_iff.mp hp).1
    · intro i hi
      obtain ⟨x, selected, unique⟩ := each i hi
      exact ⟨x, (entry i x).mpr ⟨hi, selected⟩,
        fun y hy => unique y ((entry i y).mp hy).2⟩
  exact ⟨tuple, memFunction, entry⟩

theorem sequenceFromRelation {length bound : V} (ordinal : IsOrdinal length)
    {R : V → V → Prop} (defR : ℒₛₑₜ-relation R)
    (each : ∀ i ∈ length, ∃! x, x ∈ bound ∧ R i x) :
    ∃ s, Seq s ∧ lh s = length ∧ range s ⊆ bound ∧ ∀ i ∈ length, R i (znth s i) := by
  obtain ⟨tuple, memFunction, entry⟩ := functionFromRelation defR each
  have domainEq := domain_eq_of_mem_function memFunction
  have sequence : Seq tuple := ⟨IsFunction.of_mem memFunction, length, domainEq, ordinal⟩
  have arity := sequence.lh_eq_of domainEq
  refine ⟨tuple, sequence, arity, fun x member => ?_, fun i inside => ?_⟩
  · obtain ⟨i, read⟩ := mem_range_iff.mp member
    exact ((entry i x).mp read).2.1
  · have index : i ∈ lh tuple := arity.symm ▸ inside
    exact ((entry i _).mp (sequence.znth index)).2.2

theorem sequenceFromFunction [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {length : V} (ordinal : IsOrdinal length)
    (entry : V → V) (entryDef : ℒₛₑₜ-function₁ entry) :
    ∃ s, Seq s ∧ lh s = length ∧ ∀ i ∈ length, znth s i = entry i := by
  let values := repl entry entryDef length
  have graph : ℒₛₑₜ-relation (fun i z => z = entry i) := by definability
  have each (i : V) (hi : i ∈ length) : ∃! z, z ∈ values ∧ z = entry i :=
    ⟨entry i, ⟨(repl_spec entryDef).mpr ⟨i, hi, rfl⟩, rfl⟩, fun _ h => h.2⟩
  obtain ⟨s, seq, len, _, reads⟩ := sequenceFromRelation ordinal graph each
  exact ⟨s, seq, len, reads⟩

end I0451.Logic.ZFModel
