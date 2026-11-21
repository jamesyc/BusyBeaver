module
public import I0451.Logic.SetFormulaPrograms

/-! A model-internal satisfaction table for any finite formula word.
Each entry is a set of satisfying parameter tuples. The table exists
and is unique by induction within the set model's natural numbers. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.ZFModel (ofNat_injective)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def NodeSatisfies (d word index table args : V) : Prop :=
  let kind := nodeKind word index
  let x := firstOperand word index
  let y := secondOperand word index
  (kind = SetTheory.ofNat 0 ∧ znth args x ∈ znth args y) ∨
  (kind = SetTheory.ofNat 1 ∧ znth args x = znth args y) ∨
  (kind = SetTheory.ofNat 3 ∧ (args ∈ znth table x → args ∈ znth table y)) ∨
  (kind = SetTheory.ofNat 4 ∧ ∃ value ∈ d, (args ⁀' value) ∈ znth table x) ∨
  (kind = SetTheory.ofNat 5 ∧ ∃ value ∈ d, value ∈ znth args y ∧ (args ⁀' value) ∈ znth table x)

def nodeSatisfactionDef : SetTheorySemisentence 5 :=
  f“d word index table args.
    ∃ tag x y, !kindDef tag word index ∧ !firstDef x word index ∧ !secondDef y word index ∧
      ((!(finiteOrdinalDef 0) tag ∧ !znth.dfn args x ∈ !znth.dfn args y) ∨
       (!(finiteOrdinalDef 1) tag ∧ !znth.dfn args x = !znth.dfn args y) ∨
       (!(finiteOrdinalDef 3) tag ∧ (args ∈ !znth.dfn table x → args ∈ !znth.dfn table y)) ∨
       (!(finiteOrdinalDef 4) tag ∧ (∃ value ∈ d, !seqCons.dfn args value ∈ !znth.dfn table x)) ∨
       (!(finiteOrdinalDef 5) tag ∧ ∃ value ∈ d, value ∈ !znth.dfn args y ∧
          !seqCons.dfn args value ∈ !znth.dfn table x))”

theorem nodeSatisfaction_defines :
    Defined (fun v : Fin 5 → V => NodeSatisfies (v 0) (v 1) (v 2) (v 3) (v 4)) nodeSatisfactionDef :=
  .mk fun v => by
    simp [nodeSatisfactionDef, NodeSatisfies, kind_defines.iff, first_defines.iff, second_defines.iff,
      (finiteOrdinal_defined (V := V) _).iff, znth.defined.iff, seqCons.defined.iff]
    rfl

theorem nodeSatisfies_at (d word : V) :
    ℒₛₑₜ-relation₃ (fun index table args => NodeSatisfies d word index table args) := by
  let slots : Fin 5 → (Fin 3 → V) → V := ![fun _ => d, fun _ => word, fun v => v 0, fun v => v 1, fun v => v 2]
  have each (i : Fin 5) : Language.DefinableFunction ℒₛₑₜ (slots i) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> dsimp [slots] <;> definability
  exact Language.Definable.substitution (f := slots) nodeSatisfaction_defines.to_definable each

private theorem implication_operands {word index : V} (shape : IsFormulaNode word index)
    (tag : nodeKind word index = 3) : firstOperand word index ∈ index ∧ secondOperand word index ∈ index := by
  rcases shape.2 with ⟨op, _, _⟩ | ⟨op, _, _⟩ | op |
    ⟨_, first, second, _, _⟩ | ⟨op, _, _⟩ | ⟨op, _, _, _⟩
  · have impossible : (3 : Nat) = 0 := ofNat_injective (tag.symm.trans op)
    omega
  · have impossible : (3 : Nat) = 1 := ofNat_injective (tag.symm.trans op)
    omega
  · have impossible : (3 : Nat) = 2 := ofNat_injective (tag.symm.trans op)
    omega
  · exact ⟨first, second⟩
  · have impossible : (3 : Nat) = 4 := ofNat_injective (tag.symm.trans op)
    omega

  · have impossible : (3 : Nat) = 5 := ofNat_injective (tag.symm.trans op)
    omega

private theorem quantifier_operand {word index : V} (shape : IsFormulaNode word index) {tag : Nat}
    (quantifier : tag = 4 ∨ tag = 5) (op : nodeKind word index = SetTheory.ofNat tag) :
    firstOperand word index ∈ index := by
  rcases shape.2 with ⟨kind, _, _⟩ | ⟨kind, _, _⟩ | kind | ⟨kind, _, _, _, _⟩ |
    ⟨_, first, _⟩ | ⟨_, first, _, _⟩
  · have impossible : tag = 0 := ofNat_injective (op.symm.trans kind)
    omega
  · have impossible : tag = 1 := ofNat_injective (op.symm.trans kind)
    omega
  · have impossible : tag = 2 := ofNat_injective (op.symm.trans kind)
    omega
  · have impossible : tag = 3 := ofNat_injective (op.symm.trans kind)
    omega
  · exact first
  · exact first

theorem NodeSatisfies.congr {d word index before after args : V} (shape : IsFormulaNode word index)
    (same : ∀ j ∈ index, znth before j = znth after j) :
    NodeSatisfies d word index before args ↔ NodeSatisfies d word index after args := by
  let kind := nodeKind word index
  let x := firstOperand word index
  let y := secondOperand word index
  have implication :
      (kind = SetTheory.ofNat 3 ∧ (args ∈ znth before x → args ∈ znth before y)) ↔
      (kind = SetTheory.ofNat 3 ∧ (args ∈ znth after x → args ∈ znth after y)) := by
    by_cases selected : kind = SetTheory.ofNat 3
    · have refs := implication_operands shape selected
      simp only [same x refs.1, same y refs.2]
    · simp [selected]
  have existential :
      (kind = SetTheory.ofNat 4 ∧ ∃ v ∈ d, (args ⁀' v) ∈ znth before x) ↔
      (kind = SetTheory.ofNat 4 ∧ ∃ v ∈ d, (args ⁀' v) ∈ znth after x) := by
    by_cases selected : kind = SetTheory.ofNat 4
    · rw [same x (quantifier_operand shape (.inl rfl) selected)]
    · simp [selected]
  have bounded :
      (kind = SetTheory.ofNat 5 ∧ ∃ v ∈ d, v ∈ znth args y ∧ (args ⁀' v) ∈ znth before x) ↔
      (kind = SetTheory.ofNat 5 ∧ ∃ v ∈ d, v ∈ znth args y ∧ (args ⁀' v) ∈ znth after x) := by
    by_cases selected : kind = SetTheory.ofNat 5
    · rw [same x (quantifier_operand shape (.inr rfl) selected)]
    · simp [selected]
  exact or_congr Iff.rfl (or_congr Iff.rfl (or_congr implication (or_congr existential bounded)))

structure EvaluationPrefix (d word count table : V) : Prop where
  sequence : Seq table
  length : lh table = count
  evaluates : ∀ index ∈ count, ∀ args,
    args ∈ znth table index ↔ args ∈ tupleUniverse d ∧
      lh args = nodeArity word index ∧ NodeSatisfies d word index table args

def evaluationPrefixDef : SetTheorySemisentence 4 :=
  “d word count table. !seq.dfn table ∧ !lh.dfn count table ∧
    ∀ index ∈ count, ∀ args, ∃ values, !znth.dfn values table index ∧
     (args ∈ values ↔ !tupleUniverseDef d args ∧
       (∃ n, !lh.dfn n args ∧ !arityDef n word index) ∧ !nodeSatisfactionDef d word index table args)”

theorem evaluationPrefix_defines :
    Defined (fun v : Fin 4 → V => EvaluationPrefix (v 0) (v 1) (v 2) (v 3)) evaluationPrefixDef :=
  .mk fun v => by
    simp [evaluationPrefixDef, seq.defined.iff, lh.defined.iff, znth.defined.iff,
      tupleUniverse_defines.iff, arity_defines.iff, nodeSatisfaction_defines.iff]
    exact ⟨fun ⟨seq, count, meaning⟩ => ⟨seq, count.symm, meaning⟩,
      fun h => ⟨h.sequence, h.length.symm, h.evaluates⟩⟩

private theorem evaluationPrefix_defined (d word : V) :
    ℒₛₑₜ-relation (EvaluationPrefix d word) := by
  let slots : Fin 4 → (Fin 2 → V) → V := ![fun _ => d, fun _ => word, fun v => v 0, fun v => v 1]
  have each (i : Fin 4) : Language.DefinableFunction ℒₛₑₜ (slots i) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> dsimp [slots] <;> definability
  exact Language.Definable.substitution (f := slots) evaluationPrefix_defines.to_definable each

theorem EvaluationPrefix.append {d word count table : V} (wf : IsFormulaWord word)
    (available : count ∈ lh word) (before : EvaluationPrefix d word count table) :
    ∃ next, EvaluationPrefix d word (succ count) next := by
  let Sat (args : V) := lh args = nodeArity word count ∧ NodeSatisfies d word count table args
  have SatDef : ℒₛₑₜ-predicate Sat := by
    have semantics := nodeSatisfies_at d word
    unfold Sat
    definability
  let values := sep (tupleUniverse d) Sat SatDef
  let next := table ⁀' values
  have seq := before.sequence.seqCons values
  have old (i : V) (hi : i ∈ count) : znth table i = znth next i := by
    have lt : i ∈ lh table := before.length.symm ▸ hi
    exact (seq.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt lt).mpr (before.sequence.znth lt))).symm
  refine ⟨next, seq, by rw [before.sequence.lh_seqCons, before.length], ?_⟩
  intro i hi args
  rcases mem_succ_iff.mp hi with sameIndex | earlier
  · subst i
    have here : znth next count = values := by
      have read := seq.znth_eq_of_mem (Seq.mem_seqCons table values)
      rwa [before.length] at read
    rw [here, show values = _ from rfl, mem_sep_iff]
    exact and_congr Iff.rfl (and_congr Iff.rfl (NodeSatisfies.congr (wf.2.2 count available) old))
  · let lengthOrdinal : IsOrdinal (lh word) := isOrdinal_lh _
    have beforeCount := lengthOrdinal.toIsTransitive.transitive _ available _ earlier
    rw [← old i earlier, before.evaluates i earlier args]
    have sameInputs (j : V) (inside : j ∈ i) : znth table j = znth next j := by
      let : IsOrdinal (lh word) := lengthOrdinal
      have countOrdinal : IsOrdinal count := IsOrdinal.of_mem available
      exact old j (countOrdinal.toIsTransitive.transitive _ earlier _ inside)
    exact and_congr Iff.rfl (and_congr Iff.rfl (NodeSatisfies.congr (wf.2.2 i beforeCount) sameInputs))

theorem evaluation_exists (d : V) {word : V} (wf : IsFormulaWord word) :
    ∃ table, EvaluationPrefix d word (lh word) table := by
  let P (n : V) := n ⊆ lh word → ∃ table, EvaluationPrefix d word n table
  have each : ∀ n ∈ (ω : V), P n := by
    apply naturalNumber_induction P
    · have representation := evaluationPrefix_defined d word
      unfold P
      definability
    · intro _
      refine ⟨∅, seq_empty, by simp [zero_def], ?_⟩
      intro index impossible
      simp [zero_def] at impossible
    · intro n _ ih fits
      have smaller : n ⊆ lh word := fun x hx => fits x (mem_succ_iff.mpr (.inr hx))
      obtain ⟨table, prior⟩ := ih smaller
      exact prior.append wf (fits n (mem_succ_self _))
  exact each (lh word) wf.2.1 (subset_refl _)

theorem EvaluationPrefix.on_tuple {d word table i args : V} (wf : IsFormulaWord word)
    (ev : EvaluationPrefix d word (lh word) table) (within : i ∈ lh word)
    (tuple : Tuple d args (nodeArity word i)) :
    args ∈ znth table i ↔ NodeSatisfies d word i table args := by
  have nNat : lh args ∈ (ω : V) := tuple.2.1.symm ▸ (wf.2.2 i within).1
  have inside := (mem_tupleUniverse d args).mpr ⟨tuple.1, nNat, tuple.2.2⟩
  rw [ev.evaluates i within, and_iff_right inside, and_iff_right tuple.2.1]

private theorem unequalEntries_defined (length before after : V) :
    ℒₛₑₜ-predicate (fun i => i ∈ length ∧ znth before i ≠ znth after i) := by
  definability

theorem EvaluationPrefix.unique {d word count a b : V} (wf : IsFormulaWord word) (available : count ⊆ lh word)
    (first : EvaluationPrefix d word count a) (second : EvaluationPrefix d word count b) : a = b := by
  classical
  have same : ∀ index ∈ count, znth a index = znth b index := by
    by_contra! failure
    let P (i : V) := i ∈ count ∧ znth a i ≠ znth b i
    have some : ∃ i : Ordinal V, P i := by
      obtain ⟨i, inside, diff⟩ := failure
      let : IsOrdinal count := first.length ▸ isOrdinal_lh a
      exact ⟨(IsOrdinal.of_mem inside).toOrdinal, inside, diff⟩
    obtain ⟨i, discrepancy, least⟩ := exists_minimal P (unequalEntries_defined count a b) some
    apply discrepancy.2
    have prior (j : V) (earlier : j ∈ (i : V)) : znth a j = znth b j := by
      by_contra failed
      let ordinalJ := (IsOrdinal.of_mem earlier).toOrdinal
      have inside := (show IsOrdinal count from first.length ▸ isOrdinal_lh a).toIsTransitive.transitive
        i.val discrepancy.1 j earlier
      exact not_lt_of_ge (least ordinalJ ⟨inside, failed⟩) (show ordinalJ < i from earlier)
    apply mem_ext_iff.mpr
    intro args
    rw [first.evaluates i discrepancy.1, second.evaluates i discrepancy.1]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (NodeSatisfies.congr (wf.2.2 _ (available _ discrepancy.1)) prior))
  apply Seq.lh_ext first.sequence second.sequence (first.length.trans second.length.symm)
  intro i x y left right
  have inside : i ∈ count := first.length ▸ first.sequence.lt_lh_of_mem left
  exact (first.sequence.znth_eq_of_mem left).symm.trans
    ((same i inside).trans (second.sequence.znth_eq_of_mem right))

def Satisfies (d word index args : V) : Prop :=
  ∃ table, EvaluationPrefix d word (lh word) table ∧ args ∈ znth table index

def satisfiesDef : SetTheorySemisentence 4 :=
  “d word index args. ∃ length table values, !lh.dfn length word ∧
    !evaluationPrefixDef d word length table ∧ !znth.dfn values table index ∧ args ∈ values”

theorem satisfies_defines :
    Defined (fun v : Fin 4 → V => Satisfies (v 0) (v 1) (v 2) (v 3)) satisfiesDef :=
  .mk fun v => by simp [satisfiesDef, Satisfies, lh.defined.iff, evaluationPrefix_defines.iff, znth.defined.iff]

theorem Satisfies.iff_mem {d word index args table : V} (wf : IsFormulaWord word)
    (evaluation : EvaluationPrefix d word (lh word) table) :
    Satisfies d word index args ↔ args ∈ znth table index := by
  constructor
  · rintro ⟨another, earlier, member⟩
    have unique := earlier.unique wf (subset_refl _) evaluation
    exact unique ▸ member
  · intro member
    exact ⟨table, evaluation, member⟩

theorem NodeSatisfies.atomic_mem {d word index table args : V} (op : nodeKind word index = 0) :
    NodeSatisfies d word index table args ↔ znth args (firstOperand word index) ∈ znth args (secondOperand word index) := by
  change nodeKind word index = SetTheory.ofNat 0 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem NodeSatisfies.atomic_eq {d word index table args : V} (op : nodeKind word index = 1) :
    NodeSatisfies d word index table args ↔ znth args (firstOperand word index) = znth args (secondOperand word index) := by
  change nodeKind word index = SetTheory.ofNat 1 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem NodeSatisfies.falsity {d word index table args : V} (op : nodeKind word index = 2) :
    NodeSatisfies d word index table args ↔ False := by
  change nodeKind word index = SetTheory.ofNat 2 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem NodeSatisfies.implication {d word index table args : V} (op : nodeKind word index = 3) :
    NodeSatisfies d word index table args ↔
      (args ∈ znth table (firstOperand word index) → args ∈ znth table (secondOperand word index)) := by
  change nodeKind word index = SetTheory.ofNat 3 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem NodeSatisfies.existential {d word index table args : V} (op : nodeKind word index = 4) :
    NodeSatisfies d word index table args ↔
      ∃ x ∈ d, (args ⁀' x) ∈ znth table (firstOperand word index) := by
  change nodeKind word index = SetTheory.ofNat 4 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem NodeSatisfies.boundedExistential {d word index table args : V} (op : nodeKind word index = 5) :
    NodeSatisfies d word index table args ↔
      ∃ x ∈ d, x ∈ znth args (secondOperand word index) ∧ (args ⁀' x) ∈ znth table (firstOperand word index) := by
  change nodeKind word index = SetTheory.ofNat 5 at op
  simp [NodeSatisfies, op, (ofNat_injective (V := V)).eq_iff]

theorem Satisfies.leaf {d word i args : V} (well : IsFormulaWord word) (inside : i ∈ lh word)
    (params : Tuple d args (nodeArity word i)) {result : Prop}
    (operation : ∀ table, NodeSatisfies d word i table args ↔ result) :
    Satisfies d word i args ↔ result := by
  obtain ⟨table, meaning⟩ := evaluation_exists d well
  exact (Satisfies.iff_mem well meaning).trans ((meaning.on_tuple well inside params).trans (operation table))

theorem Satisfies.implication {d word i args : V} (well : IsFormulaWord word) (inside : i ∈ lh word)
    (params : Tuple d args (nodeArity word i)) (tag : nodeKind word i = 3) :
    Satisfies d word i args ↔
      (Satisfies d word (firstOperand word i) args → Satisfies d word (secondOperand word i) args) := by
  obtain ⟨table, meaning⟩ := evaluation_exists d well
  rw [Satisfies.iff_mem well meaning, Satisfies.iff_mem well meaning, Satisfies.iff_mem well meaning,
    meaning.on_tuple well inside params, NodeSatisfies.implication tag]

theorem Satisfies.existential {d word i args : V} (well : IsFormulaWord word) (inside : i ∈ lh word)
    (params : Tuple d args (nodeArity word i)) (tag : nodeKind word i = 4) :
    Satisfies d word i args ↔ ∃ value ∈ d, Satisfies d word (firstOperand word i) (args ⁀' value) := by
  obtain ⟨table, meaning⟩ := evaluation_exists d well
  rw [Satisfies.iff_mem well meaning, meaning.on_tuple well inside params, NodeSatisfies.existential tag]
  simp only [Satisfies.iff_mem well meaning]

end I0451.Logic.SetFormulaPrograms
