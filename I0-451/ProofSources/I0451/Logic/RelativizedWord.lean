module
public import I0451.Logic.SetSequencePrepend
public import I0451.Logic.SetFormulaPrograms
public import I0451.Logic.SetSequences

/-! Compile a formula word with a leading domain parameter. Each
unbounded existential becomes a bounded existential at that parameter.
Node references stay at their original positions. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.ZFModel
open ZF207.OmegaInterpretation (omega_succ_lt_succ)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def relativeEntry (word i : V) : V := by
  classical
  let n := succ (nodeArity word i)
  let tag := nodeKind word i
  let x := firstOperand word i
  let y := secondOperand word i
  exact if tag = SetTheory.ofNat 0 ∨ tag = SetTheory.ofNat 1 then nodeRecord n tag (succ x) (succ y)
    else if tag = SetTheory.ofNat 4 then nodeRecord n 5 x 0
    else if tag = SetTheory.ofNat 5 then nodeRecord n 5 x (succ y)
    else nodeRecord n tag x y

private theorem relativeEntry_defined (word : V) : ℒₛₑₜ-function₁ (relativeEntry word) := by
  classical
  let n (i : V) := succ (nodeArity word i)
  let tag (i : V) := nodeKind word i
  let x (i : V) := firstOperand word i
  let y (i : V) := secondOperand word i
  have arities := nodeArity_defined (V := V)
  have kinds := nodeKind_defined (V := V)
  have first := firstOperand_defined (V := V)
  have second := secondOperand_defined (V := V)
  have nDef : ℒₛₑₜ-function₁ n := by unfold n; definability
  have tagDef : ℒₛₑₜ-function₁ tag := by unfold tag; definability
  have xDef : ℒₛₑₜ-function₁ x := by unfold x; definability
  have yDef : ℒₛₑₜ-function₁ y := by unfold y; definability
  let atom (i : V) : Prop := tag i = SetTheory.ofNat 0 ∨ tag i = SetTheory.ofNat 1
  have graph : ℒₛₑₜ-relation (fun z i : V =>
    (atom i ∧ z = nodeRecord (n i) (tag i) (succ (x i)) (succ (y i))) ∨
    (¬atom i ∧ tag i = SetTheory.ofNat 4 ∧ z = nodeRecord (n i) 5 (x i) 0) ∨
    (¬atom i ∧ tag i ≠ SetTheory.ofNat 4 ∧ tag i = SetTheory.ofNat 5 ∧ z = nodeRecord (n i) 5 (x i) (succ (y i))) ∨
    (¬atom i ∧ tag i ≠ SetTheory.ofNat 4 ∧ tag i ≠ SetTheory.ofNat 5 ∧ z = nodeRecord (n i) (tag i) (x i) (y i))) := by
    unfold atom nodeRecord
    definability
  exact graph.of_iff fun v => by
    change v 0 = relativeEntry word (v 1) ↔ _
    unfold relativeEntry
    change (v 0 =
      (if atom (v 1) then nodeRecord (n (v 1)) (tag (v 1)) (succ (x (v 1))) (succ (y (v 1)))
       else if tag (v 1) = SetTheory.ofNat 4 then nodeRecord (n (v 1)) 5 (x (v 1)) 0
       else if tag (v 1) = SetTheory.ofNat 5 then nodeRecord (n (v 1)) 5 (x (v 1)) (succ (y (v 1)))
       else nodeRecord (n (v 1)) (tag (v 1)) (x (v 1)) (y (v 1)))) ↔ _
    by_cases atomic : atom (v 1) <;> by_cases unbounded : tag (v 1) = SetTheory.ofNat 4 <;>
      by_cases bounded : tag (v 1) = SetTheory.ofNat 5 <;> simp [atomic, unbounded, bounded, (ofNat_injective (V := V)).eq_iff]

structure RelativizedWord (word result : V) : Prop where
  sequence : Seq result
  length : lh result = lh word
  entries : ∀ i ∈ lh word, znth result i = relativeEntry word i

theorem relativizedWord_exists (word : V) : ∃ result, RelativizedWord word result := by
  obtain ⟨result, seq, len, entries⟩ :=
    sequenceFromFunction (isOrdinal_lh word) (relativeEntry word) (relativeEntry_defined word)
  exact ⟨result, seq, len, entries⟩

theorem RelativizedWord.arity {word result i : V} (compiled : RelativizedWord word result)
    (inside : i ∈ lh word) : nodeArity result i = succ (nodeArity word i) := by
  have code := compiled.entries i inside
  unfold relativeEntry at code
  dsimp only at code
  split at code
  · exact (nodeRecord_fields code).1
  · split at code
    · exact (nodeRecord_fields code).1
    · split at code <;> exact (nodeRecord_fields code).1

theorem RelativizedWord.atom {word result i : V} (compiled : RelativizedWord word result) (inside : i ∈ lh word)
    {tag : V} (atTag : nodeKind word i = tag) (atomic : tag = 0 ∨ tag = 1) :
    nodeKind result i = tag ∧ firstOperand result i = succ (firstOperand word i) ∧
      secondOperand result i = succ (secondOperand word i) := by
  have code : znth result i = nodeRecord (succ (nodeArity word i)) tag
      (succ (firstOperand word i)) (succ (secondOperand word i)) := by
    rw [compiled.entries i inside]
    have isAtom : nodeKind word i = SetTheory.ofNat 0 ∨ nodeKind word i = SetTheory.ofNat 1 :=
      atomic.imp (fun h => atTag.trans h) (fun h => atTag.trans h)
    simp only [relativeEntry, ite_eq_left isAtom, atTag]
  exact (nodeRecord_fields code).2

theorem RelativizedWord.other {word result i : V} (compiled : RelativizedWord word result)
    (inside : i ∈ lh word) {tag : V} (atTag : nodeKind word i = tag)
    (regular : tag = 2 ∨ tag = 3) :
    nodeKind result i = tag ∧ firstOperand result i = firstOperand word i ∧
      secondOperand result i = secondOperand word i := by
  have code : znth result i = nodeRecord (succ (nodeArity word i)) tag
      (firstOperand word i) (secondOperand word i) := by
    rw [compiled.entries i inside]
    rcases regular with rfl | rfl
    · have two : nodeKind word i = SetTheory.ofNat 2 := atTag
      simp [relativeEntry, two, (ofNat_injective (V := V)).eq_iff]
      rfl
    · have three : nodeKind word i = SetTheory.ofNat 3 := atTag
      simp [relativeEntry, three, (ofNat_injective (V := V)).eq_iff]
      rfl
  exact (nodeRecord_fields code).2

theorem RelativizedWord.unbounded {word result i : V} (compiled : RelativizedWord word result)
    (inside : i ∈ lh word) (atTag : nodeKind word i = 4) :
    nodeKind result i = 5 ∧ firstOperand result i = firstOperand word i ∧ secondOperand result i = 0 := by
  have code : znth result i = nodeRecord (succ (nodeArity word i)) 5 (firstOperand word i) 0 := by
    rw [compiled.entries i inside]
    have four : nodeKind word i = SetTheory.ofNat 4 := atTag
    simp [relativeEntry, four, (ofNat_injective (V := V)).eq_iff]
  exact (nodeRecord_fields code).2

theorem RelativizedWord.bounded {word result i : V} (compiled : RelativizedWord word result)
    (inside : i ∈ lh word) (atTag : nodeKind word i = 5) :
    nodeKind result i = 5 ∧ firstOperand result i = firstOperand word i ∧
      secondOperand result i = succ (secondOperand word i) := by
  have code : znth result i = nodeRecord (succ (nodeArity word i)) 5
      (firstOperand word i) (succ (secondOperand word i)) := by
    rw [compiled.entries i inside]
    have five : nodeKind word i = SetTheory.ofNat 5 := atTag
    simp [relativeEntry, five, (ofNat_injective (V := V)).eq_iff]
  exact (nodeRecord_fields code).2

theorem RelativizedWord.wellFormed {word result : V} (compiled : RelativizedWord word result)
    (wf : IsFormulaWord word) : IsFormulaWord result := by
  refine ⟨compiled.sequence, compiled.length.symm ▸ wf.2.1, fun i available => ?_⟩
  have inside : i ∈ lh word := compiled.length ▸ available
  have old := wf.2.2 i inside
  have arity := compiled.arity inside
  let : IsOrdinal (lh word) := isOrdinal_lh _
  have earlier (x : V) (before : x ∈ i) : x ∈ lh word :=
    (show IsOrdinal (lh word) from inferInstance).toIsTransitive.transitive _ inside _ before
  have moveSlot (k : V) (pos : k ∈ nodeArity word i) : succ k ∈ nodeArity result i := by
    have kNat := (show IsTransitive (ω : V) from inferInstance).transitive _ old.1 _ pos
    rw [arity]
    exact omega_succ_lt_succ _ _ kNat old.1 pos
  have stages (j : V) (prior : j ∈ i) : nodeArity result j = succ (nodeArity word j) :=
    compiled.arity (earlier j prior)
  have nNat : nodeArity result i ∈ (ω : V) := arity.symm ▸ ω_succ_closed old.1
  refine ⟨nNat, ?_⟩
  rcases old.2 with ⟨mem, x, y⟩ | ⟨eq, x, y⟩ | bot | ⟨imp, x, y, arityX, arityY⟩ |
    ⟨ex, x, arityX⟩ | ⟨bounded, x, y, arityX⟩
  · obtain ⟨tag, left, right⟩ := compiled.atom inside mem (.inl rfl)
    exact .inl ⟨tag, left.symm ▸ moveSlot _ x, right.symm ▸ moveSlot _ y⟩
  · obtain ⟨tag, left, right⟩ := compiled.atom inside eq (.inr rfl)
    exact .inr (.inl ⟨tag, left.symm ▸ moveSlot _ x, right.symm ▸ moveSlot _ y⟩)
  · exact .inr (.inr (.inl (compiled.other inside bot (.inl rfl)).1))
  · obtain ⟨tag, left, right⟩ := compiled.other inside imp (.inr rfl)
    refine .inr (.inr (.inr (.inl ⟨tag, left.symm ▸ x, right.symm ▸ y, ?_, ?_⟩)))
    · rw [left, stages _ x, arityX, arity]
    · rw [right, stages _ y, arityY, arity]
  · obtain ⟨tag, left, right⟩ := compiled.unbounded inside ex
    have zero := (cases_mem_succ_nat old.1).1
    refine .inr (.inr (.inr (.inr (.inr ⟨tag, left.symm ▸ x, right.symm ▸ (arity.symm ▸ zero), ?_⟩))))
    rw [left, stages _ x, arityX, arity]
  · obtain ⟨tag, left, right⟩ := compiled.bounded inside bounded
    refine .inr (.inr (.inr (.inr (.inr ⟨tag, left.symm ▸ x, right.symm ▸ moveSlot _ y, ?_⟩))))
    rw [left, stages _ x, arityX, arity]

end I0451.Logic.SetFormulaPrograms
