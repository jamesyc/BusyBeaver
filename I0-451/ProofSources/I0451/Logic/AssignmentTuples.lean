module
public import I0451.Logic.SetAssignments
public import I0451.Logic.SetSequences

/-! Internal finite parameter lists read from a total assignment.
Order and repeated labels are preserved when forming the argument tuple. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

structure ReadsTuple (g labels values : V) : Prop where
  sequence : Seq values
  length : lh values = lh labels
  each : ∀ i ∈ lh labels, At E g (znth labels i) (znth values i)

def readsTupleDef : SetTheorySemisentence 3 :=
  “g labels values. !seq.dfn values ∧ ∃ n,
    !lh.dfn n labels ∧ !lh.dfn n values ∧
    ∀ i ∈ n, ∃ label value, !znth.dfn label labels i ∧ !znth.dfn value values i ∧ !atDef g label value”

theorem readsTuple_defines :
    Defined (fun v : Fin 3 → V => ReadsTuple (v 0) (v 1) (v 2)) readsTupleDef :=
  .mk fun v => by
    simp [readsTupleDef, seq.defined.iff, lh.defined.iff, znth.defined.iff, at_defines.iff]
    exact ⟨fun ⟨valid, length, reads⟩ => ⟨valid, length.symm, reads⟩,
      fun h => ⟨h.sequence, h.length.symm, h.each⟩⟩

theorem readsTuple_defined :
    ℒₛₑₜ-relation₃[V] (ReadsTuple : V → V → V → Prop) :=
  readsTuple_defines.to_definable

theorem lookup_unique {d g label : V} (gU : g ∈ assignments d) (labelD : label ∈ d) :
    ∃! x, x ∈ d ∧ At E g label x := by
  let ops := ZFModel.setOperations (V := V)
  obtain ⟨f, code⟩ := (is_map_iff_encodes ops).mp ((mem_universe d _).mp gU)
  let index : Domain E d := ⟨label, labelD⟩
  refine ⟨(f index).val, ⟨(f index).property, (code.at_iff index _).mpr rfl⟩, fun x value => ?_⟩
  exact ((code.at_iff index _).mp value.2).symm

theorem readsTuple_exists {d g labels : V} (gU : g ∈ assignments d) (sequence : Seq labels)
    (inDomain : range labels ⊆ d) :
    ∃ values, ReadsTuple g labels values ∧ range values ⊆ d := by
  let R (i x : V) := At E g (znth labels i) x
  have defR : ℒₛₑₜ-relation R := by
    have readings := At_definable (V := V)
    unfold R
    definability
  have existsEntry (i : V) (iIn : i ∈ lh labels) : ∃! x, x ∈ d ∧ R i x := by
    have index : znth labels i ∈ d := inDomain _ (mem_range_iff.mpr ⟨i, sequence.znth iIn⟩)
    exact lookup_unique gU index
  obtain ⟨values, seq, len, bounded, each⟩ :=
    sequenceFromRelation (isOrdinal_lh labels) defR existsEntry
  exact ⟨values, ⟨seq, len, each⟩, bounded⟩

theorem ReadsTuple.unique {d g labels values other : V} (gU : g ∈ assignments d) (sequence : Seq labels)
    (inDomain : range labels ⊆ d) (first : ReadsTuple g labels values) (second : ReadsTuple g labels other) :
    values = other := by
  apply Seq.lh_ext first.sequence second.sequence (first.length.trans second.length.symm)
  intro i x y xAt yAt
  have index : i ∈ lh labels := first.length ▸ first.sequence.lt_lh_of_mem xAt
  have xHit := first.each i index
  have yHit := second.each i index
  rw [first.sequence.znth_eq_of_mem xAt] at xHit
  rw [second.sequence.znth_eq_of_mem yAt] at yHit
  let ops := ZFModel.setOperations (V := V)
  obtain ⟨f, code⟩ := (is_map_iff_encodes ops).mp ((mem_universe d _).mp gU)
  let label : Domain E d := ⟨znth labels i, inDomain _ (mem_range_iff.mpr ⟨i, sequence.znth index⟩)⟩
  exact ((code.at_iff label x).mp xHit).symm.trans ((code.at_iff label y).mp yHit)

theorem ReadsTuple.append {g labels values label value : V} (before : ReadsTuple g labels values)
    (labelsSeq : Seq labels) (after : At E g label value) :
    ReadsTuple g (labels ⁀' label) (values ⁀' value) := by
  have newLabels := labelsSeq.seqCons label
  have newValues := before.sequence.seqCons value
  refine ⟨newValues, by rw [before.sequence.lh_seqCons, labelsSeq.lh_seqCons, before.length], ?_⟩
  intro i iIn
  rw [labelsSeq.lh_seqCons] at iIn
  rcases mem_succ_iff.mp iIn with rfl | earlier
  · have a := newLabels.znth_eq_of_mem (Seq.mem_seqCons labels label)
    have b := newValues.znth_eq_of_mem (Seq.mem_seqCons values value)
    rw [before.length] at b
    rwa [a, b]
  · have within : i ∈ lh values := before.length.symm ▸ earlier
    have a := newLabels.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt earlier).mpr (labelsSeq.znth earlier))
    have b := newValues.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt within).mpr (before.sequence.znth within))
    rw [a, b]
    exact before.each i earlier

theorem ReadsTuple.range_subset {d g labels values : V} (gU : g ∈ assignments d) (labelsSeq : Seq labels)
    (inDomain : range labels ⊆ d) (reads : ReadsTuple g labels values) : range values ⊆ d := by
  obtain ⟨other, chosen, bound⟩ := readsTuple_exists gU labelsSeq inDomain
  have same := reads.unique gU labelsSeq inDomain chosen
  exact same.symm ▸ bound

theorem ReadsTuple.decoded_entry {d g labels values : V}
    {f : Domain E d → Domain E d} (code : Encodes E d g f)
    (reads : ReadsTuple g labels values) (i : V) (inside : i ∈ lh labels)
    (labelD : znth labels i ∈ d) :
    (f ⟨znth labels i, labelD⟩).val = znth values i :=
  (code.at_iff ⟨znth labels i, labelD⟩ _).mp (reads.each i inside)

end I0451.Logic.SetAssignments
