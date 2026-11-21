module
public import I0451.Logic.SetSequenceConcat
public import I0451.Logic.SetFormulaPrograms

/-! Add a first parameter to an internally finite tuple. This is used
when relativizing a formula word to a named transitive subdomain. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.SetFormulaPrograms
open ZF207.OmegaInterpretation (add succ_add zero_add omega_succ_lt_succ)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cases_mem_succ_nat {n : V} (natural : n ∈ (ω : V)) :
    (0 : V) ∈ succ n ∧ ∀ i ∈ succ n, i = 0 ∨ ∃ j ∈ n, i = succ j := by
  apply naturalNumber_induction (fun n => (0 : V) ∈ succ n ∧ ∀ i ∈ succ n, i = 0 ∨ ∃ j ∈ n, i = succ j)
    (by definability) _ _ n natural
  · refine ⟨mem_succ_self _, fun i mem => ?_⟩
    simpa [mem_succ_iff, zero_def] using mem
  · intro n hn prev
    refine ⟨mem_succ_iff.mpr (.inr prev.1), fun i hi => ?_⟩
    rcases mem_succ_iff.mp hi with last | earlier
    · exact .inr ⟨n, mem_succ_self _, last⟩
    · rcases prev.2 i earlier with first | ⟨j, hj, eq⟩
      · exact .inl first
      · exact .inr ⟨j, mem_succ_iff.mpr (.inr hj), eq⟩

structure Prepends (first original result : V) : Prop where
  sequence : Seq result
  length : lh result = succ (lh original)
  head : znth result 0 = first
  tail : ∀ i ∈ lh original, znth result (succ i) = znth original i

theorem prepends_defined (first : V) : ℒₛₑₜ-relation (Prepends first) := by
  have formula : ℒₛₑₜ-relation (fun original result : V => Seq result ∧ lh result = succ (lh original) ∧
      znth result 0 = first ∧ ∀ i ∈ lh original, znth result (succ i) = znth original i) := by
    definability
  exact formula.of_iff fun _ => ⟨fun h => ⟨h.sequence, h.length, h.head, h.tail⟩,
    fun ⟨seq, len, head, tail⟩ => ⟨seq, len, head, tail⟩⟩

theorem prepends_exists (first original : V) (natural : lh original ∈ (ω : V)) :
    ∃ result, Prepends first original result := by
  let front := (∅ : V) ⁀' first
  have empty : Seq (∅ : V) := seq_empty
  have sequence : Seq front := empty.seqCons _
  have length : lh front = succ (0 : V) := by
    rw [show front = (∅ : V) ⁀' first from rfl, empty.lh_seqCons, lh_empty, zero_def]
  have naturalFront : lh front ∈ (ω : V) := length.symm ▸ ω_succ_closed zero_mem_ω
  obtain ⟨result, joined⟩ := appendedSetPrefix_exists sequence naturalFront original (lh original) natural
  have adds (i : V) (hi : i ∈ (ω : V)) : add (lh front) i = succ i := by
    rw [length, succ_add _ _ hi, ZF207.OmegaInterpretation.zero_add _ hi]
  refine ⟨result, joined.sequence, joined.length.trans (adds _ natural), ?_, ?_⟩
  · rw [joined.first 0 (length.symm ▸ mem_succ_self _)]
    simpa only [lh_empty, zero_def] using sequence.znth_eq_of_mem (Seq.mem_seqCons (∅ : V) first)
  · intro i within
    have naturalI := (show IsTransitive (ω : V) from inferInstance).transitive _ natural _ within
    have read := joined.last i within
    rwa [adds i naturalI] at read

theorem Prepends.tuple {d first original result n : V} (inserted : Prepends first original result)
    (tuple : Tuple d original n) (natural : n ∈ (ω : V)) (firstD : first ∈ d) :
    Tuple d result (succ n) := by
  have length := inserted.length.trans (congrArg succ tuple.2.1)
  refine ⟨inserted.sequence, length, fun x found => ?_⟩
  obtain ⟨i, read⟩ := mem_range_iff.mp found
  have pos : i ∈ succ n := length ▸ inserted.sequence.lt_lh_of_mem read
  rcases (cases_mem_succ_nat natural).2 i pos with firstIndex | ⟨j, earlier, index⟩
  · subst i
    have value := (inserted.sequence.znth_eq_of_mem read).symm.trans inserted.head
    exact value.symm ▸ firstD
  · subst i
    have jIn : j ∈ lh original := tuple.2.1.symm ▸ earlier
    have entry := tuple.1.znth jIn
    have value := (inserted.sequence.znth_eq_of_mem read).symm.trans (inserted.tail j jIn)
    exact value.symm ▸ tuple.2.2 _ (mem_range_iff.mpr ⟨j, entry⟩)

theorem Prepends.append {first original result : V} (prepend : Prepends first original result)
    (sequence : Seq original) (natural : lh original ∈ (ω : V)) (value : V) :
    Prepends first (original ⁀' value) (result ⁀' value) := by
  let p := prepend.sequence.seqCons value
  let q := sequence.seqCons value
  refine ⟨p, by rw [prepend.sequence.lh_seqCons, sequence.lh_seqCons, prepend.length], ?_, ?_⟩
  · have inside : (0 : V) ∈ lh result := prepend.length.symm ▸ (cases_mem_succ_nat natural).1
    have read := p.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt inside).mpr (prepend.sequence.znth inside))
    exact read.trans prepend.head
  · intro i inside
    rw [sequence.lh_seqCons] at inside
    rcases mem_succ_iff.mp inside with eq | earlier
    · subst i
      have a := p.znth_eq_of_mem (Seq.mem_seqCons result value)
      rw [prepend.length] at a
      exact a.trans (q.znth_eq_of_mem (Seq.mem_seqCons original value)).symm
    · have iNat := (show IsTransitive (ω : V) from inferInstance).transitive _ natural _ earlier
      have hits : succ i ∈ lh result :=
        prepend.length.symm ▸ omega_succ_lt_succ _ _ iNat natural earlier
      have left := p.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt hits).mpr (prepend.sequence.znth hits))
      have right := q.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt earlier).mpr (sequence.znth earlier))
      exact left.trans ((prepend.tail i earlier).trans right.symm)

end I0451.Logic.ZFModel
