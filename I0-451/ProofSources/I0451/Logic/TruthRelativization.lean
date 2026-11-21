module
public import I0451.Logic.RelativizedWord
public import I0451.Logic.SetSatisfaction

/-! Correctness of relativization for internally finite formula words.
It applies in arbitrary ZF models, including those with nonstandard
formula lengths. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.ZFModel

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem relative_truth_defined (M word oldTable newTable : V) :
    ℒₛₑₜ-predicate (fun i =>
      i ∈ lh word → ∀ args, Tuple M args (nodeArity word i) → ∀ longer,
        Prepends M args longer → (args ∈ znth oldTable i ↔ longer ∈ znth newTable i)) := by
  have arities := nodeArity_defined (V := V)
  have prepends := prepends_defined M
  unfold Tuple
  definability

theorem relativized_evaluation {D M word translated oldTable newTable : V}
    (transitive : IsTransitive M) (contained : M ⊆ D) (named : M ∈ D)
    (wf : IsFormulaWord word) (compiled : RelativizedWord word translated)
    (old : EvaluationPrefix M word (lh word) oldTable)
    (new : EvaluationPrefix D translated (lh translated) newTable) :
    ∀ i ∈ lh word, ∀ args, Tuple M args (nodeArity word i) → ∀ longer,
      Prepends M args longer → (args ∈ znth oldTable i ↔ longer ∈ znth newTable i) := by
  let P (i : V) := i ∈ lh word → ∀ args, Tuple M args (nodeArity word i) → ∀ longer,
    Prepends M args longer → (args ∈ znth oldTable i ↔ longer ∈ znth newTable i)
  have defined : ℒₛₑₜ-predicate P := relative_truth_defined M word oldTable newTable
  have each : ∀ i : Ordinal V, P i := by
    apply transfinite_induction P defined
    intro i earlier inside args tuple longer expanded
    let lengthOrdinal : IsOrdinal (lh word) := isOrdinal_lh _
    have atNew : i.val ∈ lh translated := compiled.length.symm ▸ inside
    have transport : Tuple D args (nodeArity word i.val) :=
      ⟨tuple.1, tuple.2.1, subset_trans tuple.2.2 contained⟩
    have formation := wf.2.2 i.val inside
    have count := formation.1
    have hasLonger := expanded.tuple transport count named
    rw [← compiled.arity inside] at hasLonger
    have oldAnswer := old.on_tuple wf inside tuple
    have newAnswer := new.on_tuple (compiled.wellFormed wf) atNew hasLonger
    rw [oldAnswer, newAnswer]
    have prior (x : V) (before : x ∈ i.val) : P x :=
      earlier (IsOrdinal.of_mem before).toOrdinal before
    have higher (x : V) (before : x ∈ i.val) : x ∈ lh word :=
      lengthOrdinal.toIsTransitive.transitive i.val inside x before
    have reads (slot : V) (inRange : slot ∈ nodeArity word i.val) :
        znth longer (succ slot) = znth args slot := expanded.tail slot (tuple.2.1.symm ▸ inRange)
    have guard (B : V) (BInM : B ⊆ M) (body : V) (earlierBody : body ∈ i.val)
        (arityBody : nodeArity word body = succ (nodeArity word i.val)) :
        (∃ y ∈ M, y ∈ B ∧ (args ⁀' y) ∈ znth oldTable body) ↔
        ∃ y ∈ D, y ∈ B ∧ (longer ⁀' y) ∈ znth newTable body := by
      have bodyTruth (y : V) (yM : y ∈ M) :
          (args ⁀' y) ∈ znth oldTable body ↔ (longer ⁀' y) ∈ znth newTable body := by
        have argument := tuple.append yM
        rw [← arityBody] at argument
        have added := expanded.append tuple.1 (tuple.2.1.symm ▸ count) y
        exact prior body earlierBody (higher _ earlierBody) _ argument _ added
      constructor
      · rintro ⟨y, yM, yB, proof⟩
        exact ⟨y, contained _ yM, yB, (bodyTruth y yM).mp proof⟩
      · rintro ⟨y, _, yB, proof⟩
        have yM := BInM _ yB
        exact ⟨y, yM, yB, (bodyTruth y yM).mpr proof⟩
    rcases formation.2 with ⟨memory, left, right⟩ | ⟨equality, left, right⟩ | falsehood |
      ⟨implication, left, right, leftArity, rightArity⟩ |
      ⟨exists_, earlierBody, arityBody⟩ | ⟨bounded, earlierBody, boundSlot, arityBody⟩
    · obtain ⟨tag, lhs, rhs⟩ := compiled.atom inside memory (.inl rfl)
      rw [NodeSatisfies.atomic_mem memory, NodeSatisfies.atomic_mem tag, lhs, rhs, reads _ left, reads _ right]
    · obtain ⟨tag, lhs, rhs⟩ := compiled.atom inside equality (.inr rfl)
      rw [NodeSatisfies.atomic_eq equality, NodeSatisfies.atomic_eq tag, lhs, rhs, reads _ left, reads _ right]
    · rw [NodeSatisfies.falsity falsehood, NodeSatisfies.falsity (compiled.other inside falsehood (.inl rfl)).1]
    · obtain ⟨tag, lhs, rhs⟩ := compiled.other inside implication (.inr rfl)
      rw [NodeSatisfies.implication implication, NodeSatisfies.implication tag, lhs, rhs]
      exact (prior _ left (higher _ left) _ (by rwa [leftArity]) _ expanded).imp
        (prior _ right (higher _ right) _ (by rwa [rightArity]) _ expanded)
    · obtain ⟨tag, body, boundSlot⟩ := compiled.unbounded inside exists_
      rw [NodeSatisfies.existential exists_, NodeSatisfies.boundedExistential tag, body, boundSlot, expanded.head]
      have bounded := guard M (subset_refl _) _ earlierBody arityBody
      simpa only [← and_assoc, and_self] using bounded
    · obtain ⟨tag, body, boundShift⟩ := compiled.bounded inside bounded
      rw [NodeSatisfies.boundedExistential bounded, NodeSatisfies.boundedExistential tag, body, boundShift, reads _ boundSlot]
      have boundInM : znth args (secondOperand word i.val) ∈ M := by
        have within : secondOperand word i.val ∈ lh args := tuple.2.1.symm ▸ boundSlot
        exact tuple.2.2 _ (mem_range_iff.mpr ⟨_, tuple.1.znth within⟩)
      exact guard _ (transitive.transitive _ boundInM) _ earlierBody arityBody
  intro i inside
  let : IsOrdinal (lh word) := isOrdinal_lh _
  exact each (IsOrdinal.of_mem inside).toOrdinal inside

theorem relativized_satisfaction {D M word translated i args longer : V}
    (transitive : IsTransitive M) (contained : M ⊆ D) (named : M ∈ D)
    (wf : IsFormulaWord word) (compiled : RelativizedWord word translated) (inside : i ∈ lh word)
    (tuple : Tuple M args (nodeArity word i)) (expanded : Prepends M args longer) :
    Satisfies M word i args ↔ Satisfies D translated i longer := by
  obtain ⟨oldTable, old⟩ := evaluation_exists M wf
  have newWf := compiled.wellFormed wf
  obtain ⟨newTable, new⟩ := evaluation_exists D newWf
  rw [Satisfies.iff_mem wf old, Satisfies.iff_mem newWf new]
  exact relativized_evaluation transitive contained named wf compiled old new i inside args tuple longer expanded

end I0451.Logic.SetFormulaPrograms
