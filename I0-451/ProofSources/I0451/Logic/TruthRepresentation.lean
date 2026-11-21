module
public import I0451.Logic.CodedElementarity
public import I0451.Logic.TruthEquality
public import I0451.Logic.CanonicalTruthFamily

/-! Represent the satisfaction of internally finite first-order formulas
by relations in the literal generated family. Parameter tuples use
their values as labels. A bound variable gets a natural label outside
the whole parameter tuple. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

private theorem ReadsTuple.change_assignment {d g h labels values : V}
    (before : ReadsTuple g labels values) (labelsSeq : Seq labels) (inDomain : range labels ⊆ d)
    {unused : V} (fresh : unused ∉ range labels) (same : SameExcept d unused g h) :
    ReadsTuple h labels values := by
  refine ⟨before.sequence, before.length, fun i iIn => ?_⟩
  have present := mem_range_iff.mpr ⟨i, labelsSeq.znth iIn⟩
  have distinct : znth labels i ≠ unused := fun eq => fresh (eq ▸ present)
  exact (same _ (inDomain _ present) distinct _).mp (before.each i iIn)

def RepresentsNode (d word table index : V) : Prop :=
  ∀ labels, Tuple d labels (nodeArity word index) →
    ∃ relation ∈ generated d (assignments d), ∀ g ∈ assignments d, ∀ values,
      ReadsTuple g labels values → (values ∈ znth table index ↔ g ∈ relation)

private theorem representsNode_defined (d word table : V) :
    ℒₛₑₜ-predicate (RepresentsNode d word table) := by
  have arities := nodeArity_defined (V := V)
  have reading := readsTuple_defined (V := V)
  unfold RepresentsNode Tuple
  definability

private theorem node_reading {d word table index labels g values : V}
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table)
    (here : index ∈ lh word) (params : Tuple d labels (nodeArity word index))
    (inUniverse : g ∈ assignments d) (reads : ReadsTuple g labels values) :
    values ∈ znth table index ↔ NodeSatisfies d word index table values := by
  exact evaluation.on_tuple wf here
    ⟨reads.sequence, reads.length.trans params.2.1, reads.range_subset inUniverse params.1 params.2.2⟩

private theorem in_label_domain {d labels count index : V}
    (params : Tuple d labels count) (position : index ∈ count) :
    znth labels index ∈ d := by
  have read := params.1.znth (params.2.1.symm ▸ position)
  exact params.2.2 _ (mem_range_iff.mpr ⟨_, read⟩)

private theorem represent_membership {d word table i : V}
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table)
    (here : i ∈ lh word) (tag : nodeKind word i = 0)
    (xIn : firstOperand word i ∈ nodeArity word i) (yIn : secondOperand word i ∈ nodeArity word i) :
    RepresentsNode d word table i := by
  intro labels params
  let x : Domain E d := ⟨znth labels (firstOperand word i), in_label_domain params xIn⟩
  let y : Domain E d := ⟨znth labels (secondOperand word i), in_label_domain params yIn⟩
  let U := assignments d
  refine ⟨atomicSet U x.val y.val, (generated_closed d U).atom _ _ x.property y.property, ?_⟩
  intro g gU values reads
  obtain ⟨f, code⟩ := (is_map_iff_encodes ZFModel.setOperations).mp ((mem_universe d g).mp gU)
  have xRead := reads.decoded_entry code _ (params.2.1.symm ▸ xIn) x.property
  have yRead := reads.decoded_entry code _ (params.2.1.symm ▸ yIn) y.property
  rw [node_reading wf evaluation here params gU reads, NodeSatisfies.atomic_mem tag,
    atomicSet_eval_decode code gU x y, xRead, yRead]

private theorem represent_equality {d word table i : V}
    (transitive : IsTransitive d) (omega : (ω : V) ⊆ d)
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table)
    (here : i ∈ lh word) (tag : nodeKind word i = 1)
    (xIn : firstOperand word i ∈ nodeArity word i) (yIn : secondOperand word i ∈ nodeArity word i) :
    RepresentsNode d word table i := by
  intro labels params
  let x : Domain E d := ⟨znth labels (firstOperand word i), in_label_domain params xIn⟩
  let y : Domain E d := ⟨znth labels (secondOperand word i), in_label_domain params yIn⟩
  obtain ⟨R, inR, eval⟩ := generated_equality transitive omega x y
  refine ⟨R, inR, fun g gU values reads => ?_⟩
  obtain ⟨f, code⟩ := (is_map_iff_encodes ZFModel.setOperations).mp ((mem_universe d g).mp gU)
  have xRead := reads.decoded_entry code _ (params.2.1.symm ▸ xIn) x.property
  have yRead := reads.decoded_entry code _ (params.2.1.symm ▸ yIn) y.property
  rw [node_reading wf evaluation here params gU reads, NodeSatisfies.atomic_eq tag,
    eval g f code, Subtype.ext_iff, xRead, yRead]

private theorem represent_implication {d word table i : V} (omega : (ω : V) ⊆ d)
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table)
    (here : i ∈ lh word) (tag : nodeKind word i = 3)
    (xArity : nodeArity word (firstOperand word i) = nodeArity word i)
    (yArity : nodeArity word (secondOperand word i) = nodeArity word i)
    (xRep : RepresentsNode d word table (firstOperand word i))
    (yRep : RepresentsNode d word table (secondOperand word i)) :
    RepresentsNode d word table i := by
  intro labels params
  obtain ⟨R, inR, readR⟩ := xRep labels (by rwa [xArity])
  obtain ⟨S, inS, readS⟩ := yRep labels (by rwa [yArity])
  obtain ⟨T, inT, truth⟩ := generated_implication omega inR inS
  refine ⟨T, inT, fun g gU values reads => ?_⟩
  rw [node_reading wf evaluation here params gU reads, NodeSatisfies.implication tag, truth g gU,
    readR g gU values reads, readS g gU values reads]

private theorem quantifier_guard {d labels count k : V} (omega : (ω : V) ⊆ d)
    (params : Tuple d labels count) (kD : k ∈ d) (bound : Option V)
    (valid : ∀ i, bound = some i → i ∈ count) :
    ∃ S ∈ generated d (assignments d), ∀ g ∈ assignments d, ∀ values value,
      ReadsTuple g labels values → At E g k value →
      (g ∈ S ↔ ∀ i, bound = some i → value ∈ znth values i) := by
  cases bound with
  | none =>
    exact ⟨assignments d, generated_full omega, fun g gU values value _ _ => by simp [gU]⟩
  | some i =>
    let x : Domain E d := ⟨k, kD⟩
    have iIn : i ∈ count := valid i rfl
    let y : Domain E d := ⟨znth labels i, in_label_domain params iIn⟩
    let U := assignments d
    refine ⟨atomicSet U x.val y.val, (generated_closed d U).atom _ _ x.property y.property, ?_⟩
    intro g gU values value reads atX
    obtain ⟨f, code⟩ := (is_map_iff_encodes ZFModel.setOperations).mp ((mem_universe d g).mp gU)
    have left : (f x).val = value := (code.at_iff x _).mp atX
    have right := reads.decoded_entry code _ (params.2.1.symm ▸ iIn) y.property
    rw [atomicSet_eval_decode code gU x y, left, right]
    exact ⟨fun mem j eq => (Option.some.inj eq) ▸ mem, fun every => every i rfl⟩

private theorem represent_quantifier {d word table i : V} (omega : (ω : V) ⊆ d)
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table)
    (here : i ∈ lh word) (bound : Option V) (valid : ∀ j, bound = some j → j ∈ nodeArity word i)
    (spec : ∀ args, NodeSatisfies d word i table args ↔ ∃ value ∈ d,
      (∀ j, bound = some j → value ∈ znth args j) ∧ (args ⁀' value) ∈ znth table (firstOperand word i))
    (childArity : nodeArity word (firstOperand word i) = succ (nodeArity word i))
    (inner : RepresentsNode d word table (firstOperand word i)) :
    RepresentsNode d word table i := by
  classical
  intro labels params
  have short : lh labels ∈ (ω : V) := params.2.1.symm ▸ (wf.2.2 i here).1
  obtain ⟨k, natural, fresh⟩ := fresh_natural_for_sequence params.1 short
  have kD := omega k natural
  have childParams := params.append kD
  rw [← childArity] at childParams
  obtain ⟨R, inR, model⟩ := inner (labels ⁀' k) childParams
  obtain ⟨S, inS, guard⟩ := quantifier_guard omega params kD bound valid
  obtain ⟨Q, inQ, combined⟩ := generated_conjunction omega inS inR
  obtain ⟨T, inT, quantify⟩ := generated_existential omega kD inQ
  refine ⟨T, inT, fun g gU values reads => ?_⟩
  rw [node_reading wf evaluation here params gU reads, spec values, quantify g gU]
  constructor
  · rintro ⟨value, valueD, permitted, answer⟩
    obtain ⟨h, hU, hit, stays⟩ := replace_assignment_value gU kD valueD
    have other := SameExcept.of_agree kD gU hU stays
    have unchanged := reads.change_assignment params.1 params.2.2 fresh other
    have extended := unchanged.append params.1 hit
    have both := (combined h hU).mpr
      ⟨(guard h hU values value unchanged hit).mpr permitted, (model h hU _ extended).mp answer⟩
    exact ⟨h, hU, both, other⟩
  · rintro ⟨h, hU, answer, stays⟩
    obtain ⟨value, ⟨valueD, hit⟩, _⟩ := lookup_unique hU kD
    have unchanged := reads.change_assignment params.1 params.2.2 fresh stays
    obtain ⟨permitted, witnesses⟩ := (combined h hU).mp answer
    exact ⟨value, valueD, (guard h hU values value unchanged hit).mp permitted,
      (model h hU _ (unchanged.append params.1 hit)).mpr witnesses⟩

theorem represents_every_node {d word table : V} (transitive : IsTransitive d) (omega : (ω : V) ⊆ d)
    (wf : IsFormulaWord word) (evaluation : EvaluationPrefix d word (lh word) table) :
    ∀ i ∈ lh word, RepresentsNode d word table i := by
  let P (i : V) := i ∈ lh word → RepresentsNode d word table i
  have defined : ℒₛₑₜ-predicate P := by
    have representation := representsNode_defined d word table
    unfold P
    definability
  have every : ∀ i : Ordinal V, P i := by
    apply transfinite_induction P defined
    intro i earlier inside
    let lengthOrdinal : IsOrdinal (lh word) := isOrdinal_lh _
    have lower (l : V) (before : l ∈ (i : V)) : RepresentsNode d word table l :=
      earlier (IsOrdinal.of_mem before).toOrdinal before
        (lengthOrdinal.toIsTransitive.transitive i.val inside l before)
    rcases (wf.2.2 i.val inside).2 with ⟨memTag, xIn, yIn⟩ | ⟨eqTag, xIn, yIn⟩ | falseTag |
      ⟨impTag, xBefore, yBefore, xCount, yCount⟩ | ⟨exTag, childBefore, childCount⟩ |
      ⟨boundedTag, childBefore, boundIndex, childCount⟩
    · exact represent_membership wf evaluation inside memTag xIn yIn
    · exact represent_equality transitive omega wf evaluation inside eqTag xIn yIn
    · intro labels params
      exact ⟨∅, generated_empty omega, fun g gU values reads => by
        rw [node_reading wf evaluation inside params gU reads, NodeSatisfies.falsity falseTag]
        simp⟩
    · exact represent_implication omega wf evaluation inside impTag xCount yCount
        (lower _ xBefore) (lower _ yBefore)
    · apply represent_quantifier omega wf evaluation inside none (by simp) _ childCount (lower _ childBefore)
      intro args
      simp [NodeSatisfies.existential exTag]
    · refine represent_quantifier omega wf evaluation inside (some (secondOperand word i.val))
        (fun j eq => (Option.some.inj eq) ▸ boundIndex) ?_ childCount (lower _ childBefore)
      intro args
      simp [NodeSatisfies.boundedExistential boundedTag]
  intro i inside
  let : IsOrdinal (lh word) := isOrdinal_lh _
  exact every (IsOrdinal.of_mem inside).toOrdinal inside

/-- The literal comparison implies elementarity for formulas whose
syntax and parameter tuples are internally finite in the set model. -/
theorem generatedComparison_codedElementary {d j : V} (transitive : IsTransitive d)
    (omega : (ω : V) ⊆ d) (comparison : GeneratedComparison d j) : CodedElementary d j := by
  classical
  obtain ⟨inside, compares⟩ := (generatedComparison_iff_identity d j).mp comparison
  refine ⟨inside, fun word wf i within args tuple images takes => ?_⟩
  obtain ⟨table, evaluation⟩ := evaluation_exists d wf
  obtain ⟨R, inR, trace⟩ := represents_every_node transitive omega wf evaluation i within args tuple
  have original := trace (identity d) (identity_mem_universe d) args (identity_readsTuple tuple)
  have moved := trace j inside images takes
  have agreement : identity d ∈ R ↔ j ∈ R := by
    constructor
    · exact compares R inR
    · intro after
      by_contra before
      obtain ⟨S, inS, complement⟩ := generated_negation omega inR
      have opposite := (complement (identity d) (identity_mem_universe d)).mpr before
      exact (complement j inside).mp (compares S inS opposite) after
  rw [Satisfies.iff_mem wf evaluation, Satisfies.iff_mem wf evaluation, original, moved]
  exact agreement

end I0451.Logic.SetAssignments
