module
public import I0451.Logic.CodedElementarity
public import I0451.Logic.CanonicalTruthFamily
public import I0451.Logic.FormulaWordConstructors
public import I0451.Logic.SetSequenceConcat

/-! Every generated assignment relation has a formula using a finite
support of labels. A compiler takes a slot for each label and appends
its formula to an existing word. Thus two compiled subformulas share
one word without moving the node references of either. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel I0451.Logic.SetFormulaPrograms
open ZF207.OmegaInterpretation (add_mem_omega)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

private def ReadsSlots (g slots args : V) : Prop :=
  ∀ x q, ⟨x,q⟩ₖ ∈ slots → At E g x (znth args q)

private def RepresentableRelation (d R : V) : Prop :=
  ∃ support, support ∈ tupleUniverse d ∧
    ∀ n ∈ (ω : V), ∀ slots ∈ n ^ range support, ∀ before, IsFormulaWord before →
      ∃ word index, IsFormulaWord word ∧ index ∈ lh word ∧ nodeArity word index = n ∧
        FormulaPrefix before word ∧ ∀ g ∈ assignments d, ∀ args, Tuple d args n →
          ReadsSlots g slots args → (g ∈ R ↔ Satisfies d word index args)

private theorem representable_definable (d : V) : ℒₛₑₜ-predicate (RepresentableRelation d) := by
  have wf := formulaWord_defines (V := V) |>.to_definable
  have arity := nodeArity_defined (V := V)
  have sat := satisfies_defines (V := V) |>.to_definable
  have reads : ℒₛₑₜ-relation₃[V] (ReadsSlots : V → V → V → Prop) := by
    have atValue := At_definable (V := V)
    unfold ReadsSlots
    definability
  have prefixShape : ℒₛₑₜ-relation[V] (FormulaPrefix : V → V → Prop) := by
    have exactShape : ℒₛₑₜ-relation (fun before after : V => lh before ⊆ lh after ∧
        ∀ i ∈ lh before, znth after i = znth before i) := by definability
    exact exactShape.of_iff fun _ => ⟨fun h => ⟨h.length, h.entries⟩, fun ⟨a,b⟩ => ⟨a,b⟩⟩
  have tuples : ℒₛₑₜ-relation₃[V] (Tuple : V → V → V → Prop) :=
    tuple_defines.to_definable
  unfold RepresentableRelation
  definability

private theorem atomic_representable {d i k : V} (iD : i ∈ d) (kD : k ∈ d) :
    RepresentableRelation d (atomicSet (assignments d) i k) := by
  let singleton := (∅ : V) ⁀' i
  let support := singleton ⁀' k
  have empty : Seq (∅ : V) := by simp
  have singletonSeq := empty.seqCons i
  have supportSeq := singletonSeq.seqCons k
  have iEntry : ⟨lh (∅ : V), i⟩ₖ ∈ support := by
    have first := Seq.mem_seqCons (∅ : V) i
    have inside := singletonSeq.lt_lh_of_mem first
    exact (Seq.mem_seqCons_iff_of_lt inside).mpr first
  have iPresent : i ∈ range support := mem_range_iff.mpr ⟨_,iEntry⟩
  have kPresent : k ∈ range support := mem_range_iff.mpr ⟨_,Seq.mem_seqCons singleton k⟩
  have supportBound : range support ⊆ d := by
    intro x present
    obtain ⟨q, entry⟩ := mem_range_iff.mp present
    rcases kpair_mem_seqCons_iff.mp entry with ⟨_,rfl⟩ | older
    · exact kD
    · rcases kpair_mem_seqCons_iff.mp older with ⟨_,rfl⟩ | impossible
      · exact iD
      · simp at impossible
  have finite : lh support ∈ (ω : V) := by
    rw [singletonSeq.lh_seqCons, empty.lh_seqCons, lh_empty, ← zero_def]
    exact ω_succ_closed (ω_succ_closed zero_mem_ω)
  refine ⟨support, (mem_tupleUniverse d support).mpr ⟨supportSeq, finite, supportBound⟩, ?_⟩
  intro n nNat slots slotsFn before old
  obtain ⟨x, xIn, xEntry⟩ := exists_of_mem_function slotsFn i iPresent
  obtain ⟨y, yIn, yEntry⟩ := exists_of_mem_function slotsFn k kPresent
  let record := nodeRecord n 0 x y
  obtain ⟨entry, meaning⟩ := FormulaNodeAt.append_mem old nNat xIn yIn
  refine ⟨before ⁀' record, lh before, entry.formed, entry.indexMem, entry.arityEq,
    FormulaPrefix.append _ _ old.1, fun g gU args tuple aligned => ?_⟩
  have atX := aligned i x xEntry
  have atY := aligned k y yEntry
  rw [mem_atomicSet, and_iff_right gU, meaning tuple]
  obtain ⟨f, code⟩ := (is_map_iff_encodes ZFModel.setOperations).mp ((mem_universe d g).mp gU)
  constructor
  · exact fun a => a _ _ atX atY
  · intro belongs a b left right
    have sameX := ((code.at_iff ⟨i,iD⟩ _).mp left).symm.trans ((code.at_iff ⟨i,iD⟩ _).mp atX)
    have sameY := ((code.at_iff ⟨k,kD⟩ _).mp right).symm.trans ((code.at_iff ⟨k,kD⟩ _).mp atY)
    rwa [sameX, sameY]

private theorem binder_slots {n i domain sub slots : V} (included : sub ⊆ domain)
    (parent : slots ∈ n ^ domain) :
    ∃ lifted ∈ (succ n) ^ sub,
      ∀ x q, ⟨x,q⟩ₖ ∈ lifted →
        (x = i ∧ q = n) ∨ (x ≠ i ∧ ⟨x,q⟩ₖ ∈ slots) := by
  let R (x q : V) : Prop := (x = i ∧ q = n) ∨ (x ≠ i ∧ ⟨x,q⟩ₖ ∈ slots)
  have definition : ℒₛₑₜ-relation R := by unfold R; definability
  have each (x : V) (xIn : x ∈ sub) : ∃! q, q ∈ succ n ∧ R x q := by
    by_cases same : x = i
    · exact ⟨n, ⟨mem_succ_self _, .inl ⟨same,rfl⟩⟩, fun q h => (h.2.resolve_right
        (fun incompatible => incompatible.1 same)).2⟩
    · obtain ⟨q, atQ, unique⟩ := exists_unique_of_mem_function parent x (included x xIn)
      refine ⟨q, ⟨mem_succ_iff.mpr (.inr (mem_of_mem_functions parent atQ).2), .inr ⟨same,atQ⟩⟩, ?_⟩
      exact fun r h => unique r (h.2.resolve_left (fun incompatible => same incompatible.1)).2
  obtain ⟨lifted, fn, graph⟩ := functionFromRelation definition each
  exact ⟨lifted, fn, fun x q pair => ((graph x q).mp pair).2.2⟩

private theorem ReadsSlots.append {d sub n i g h slots lifted args value : V}
    (subD : sub ⊆ d) (liftedFn : lifted ∈ (succ n) ^ sub)
    (liftSpec : ∀ x q, ⟨x,q⟩ₖ ∈ lifted →
      (x = i ∧ q = n) ∨ (x ≠ i ∧ ⟨x,q⟩ₖ ∈ slots))
    (parent : ReadsSlots g slots args) {domain : V} (parentFn : slots ∈ n ^ domain)
    (tuple : Tuple d args n) (stays : SameExcept d i g h) (hits : At E h i value) :
    ReadsSlots h lifted (args ⁀' value) := by
  intro x q pair
  have seq := tuple.1.seqCons value
  rcases liftSpec x q pair with ⟨rfl,rfl⟩ | ⟨different, old⟩
  · rw [← tuple.2.1, seq.znth_eq_of_mem (Seq.mem_seqCons args value)]
    exact hits
  · have before : q ∈ lh args := tuple.2.1.symm ▸ (mem_of_mem_functions parentFn old).2
    rw [seq.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt before).mpr (tuple.1.znth before))]
    exact (stays x (subD x (mem_of_mem_functions liftedFn pair).1) different _).mp (parent x q old)

private theorem step_representable {d i R S : V} (iD : i ∈ d)
    (repR : RepresentableRelation d R) (repS : RepresentableRelation d S) :
    RepresentableRelation d (stepSet (assignments d) i R S) := by
  obtain ⟨rs, tr, compileR⟩ := repR
  obtain ⟨ss, ts, compileS⟩ := repS
  obtain ⟨rSeq, rNat, rD⟩ := (mem_tupleUniverse d rs).mp tr
  obtain ⟨sSeq, sNat, sD⟩ := (mem_tupleUniverse d ss).mp ts
  obtain ⟨support, joined⟩ := appendedSetPrefix_exists rSeq rNat ss (lh ss) sNat
  have labels := joined.range rSeq sSeq rNat sNat
  have rIncluded : range rs ⊆ range support := fun x h => labels.symm ▸ mem_union_iff.mpr (.inl h)
  have sIncluded : range ss ⊆ range support := fun x h => labels.symm ▸ mem_union_iff.mpr (.inr h)
  have supportD : range support ⊆ d := by
    intro x inside
    exact (mem_union_iff.mp (labels ▸ inside)).elim (rD x) (sD x)
  have supportNat : lh support ∈ (ω : V) := joined.length.symm ▸ add_mem_omega _ _ rNat sNat
  refine ⟨support, (mem_tupleUniverse d support).mpr ⟨joined.sequence, supportNat, supportD⟩, ?_⟩
  intro n nNat slots slotsFn before old
  obtain ⟨rSlots, rFn, rLift⟩ := binder_slots (i := i) rIncluded slotsFn
  obtain ⟨sSlots, sFn, sLift⟩ := binder_slots (i := i) sIncluded slotsFn
  have nNext := ω_succ_closed nNat
  obtain ⟨rw, ri, rWf, rIn, rCount, rPrefix, rTruth⟩ := compileR _ nNext _ rFn before old
  obtain ⟨sw, si, sWf, sIn, sCount, sPrefix, sTruth⟩ := compileS _ nNext _ sFn rw rWf
  let impRecord := nodeRecord (succ n) 3 ri si
  let impWord := sw ⁀' impRecord
  let exRecord := nodeRecord n 4 (lh sw) 0
  have left : FormulaNodeAt sw ri (succ n) :=
    ⟨sWf, sPrefix.length ri rIn, (sPrefix.fields rIn).1.trans rCount⟩
  obtain ⟨impNode, impMeaning⟩ := FormulaNodeAt.append_imp left ⟨sWf, sIn, sCount⟩
  obtain ⟨exNode, exMeaning⟩ := impNode.append_ex nNat
  have throughImp := FormulaPrefix.append sw impRecord sWf.1
  have throughEx := FormulaPrefix.append impWord exRecord impNode.formed.1
  refine ⟨impWord ⁀' exRecord, lh impWord, exNode.formed, exNode.indexMem, exNode.arityEq,
    ((rPrefix.trans sPrefix).trans throughImp).trans throughEx, fun g gU args tuple reading => ?_⟩
  rw [mem_stepSet, and_iff_right gU, exMeaning tuple]
  have implication (h : V) (hU : h ∈ assignments d) (value : V) (valueD : value ∈ d)
      (hit : At E h i value) (same : SameExcept d i g h) :
      (h ∈ R → h ∈ S) ↔ Satisfies d impWord (lh sw) (args ⁀' value) := by
    have extended := tuple.append valueD
    have left := (rTruth h hU _ extended (reading.append rD rFn rLift slotsFn tuple same hit)).trans
      (sPrefix.satisfaction rWf sWf rIn)
    have right := sTruth h hU _ extended (reading.append sD sFn sLift slotsFn tuple same hit)
    exact (left.imp right).trans (impMeaning extended).symm
  constructor
  · rintro ⟨h,hU,positive,agree⟩
    obtain ⟨value, ⟨valueD,hit⟩, _⟩ := lookup_unique hU iD
    exact ⟨value, valueD, (implication h hU value valueD hit (SameExcept.of_agree iD gU hU agree)).mp positive⟩
  · rintro ⟨value,valueD,positive⟩
    obtain ⟨h,hU,hit,agree⟩ := replace_assignment_value gU iD valueD
    exact ⟨h, hU, (implication h hU value valueD hit (SameExcept.of_agree iD gU hU agree)).mpr positive, agree⟩

private theorem generated_representable {d R : V} (member : R ∈ generated d (assignments d)) :
    RepresentableRelation d R := by
  let U := assignments d
  let family := sep (℘ U) (RepresentableRelation d) (representable_definable d)
  have contains (S : V) : S ∈ family ↔ S ⊆ U ∧ RepresentableRelation d S := by
    rw [mem_sep_iff, mem_power_iff]
  have closed : ClosedFamily d U family := {
    subset := fun S m => ((contains S).mp m).1
    atom := fun i k iD kD => (contains _).mpr
      ⟨fun g member => ((mem_atomicSet U i k g).mp member).1, atomic_representable iD kD⟩
    step := fun i R S iD rIn sIn => (contains _).mpr
      ⟨fun g member => ((mem_stepSet U i R S g).mp member).1,
        step_representable iD ((contains R).mp rIn).2 ((contains S).mp sIn).2⟩ }
  exact ((contains R).mp (((mem_generated R d U).mp member).2 family closed)).2

/-- Repeat labels can share their first output slot, even when the
support has nonstandard finite length in the model. -/
private theorem support_slots {support : V} (seq : Seq support) :
    ∃ slots ∈ (lh support) ^ range support, ∀ x q, ⟨x,q⟩ₖ ∈ slots → znth support q = x := by
  let R (x q : V) : Prop := ⟨q,x⟩ₖ ∈ support ∧ ∀ r ∈ q, ⟨r,x⟩ₖ ∉ support
  have RDef : ℒₛₑₜ-relation R := by unfold R; definability
  let : IsOrdinal (lh support) := isOrdinal_lh support
  have each (x : V) (has : x ∈ range support) : ∃! q, q ∈ lh support ∧ R x q := by
    obtain ⟨j, read⟩ := mem_range_iff.mp has
    let P (q : V) := ⟨q,x⟩ₖ ∈ support
    have PDef : ℒₛₑₜ-predicate P := by unfold P; definability
    obtain ⟨q, present, first⟩ := exists_minimal P PDef
      ⟨(IsOrdinal.of_mem (seq.lt_lh_of_mem read)).toOrdinal, read⟩
    refine ⟨q.val, ⟨seq.lt_lh_of_mem present, present, ?_⟩, ?_⟩
    · intro r earlier already
      let ord := (IsOrdinal.of_mem earlier).toOrdinal
      exact not_lt_of_ge (first ord already) (show ord < q from earlier)
    · rintro r ⟨rIn, atR, firstR⟩
      let ord := (IsOrdinal.of_mem rIn).toOrdinal
      have up : q ≤ ord := first ord atR
      have down : ord ≤ q := le_of_not_gt (fun tooSmall : q < ord => firstR q.val tooSmall present)
      exact congrArg Ordinal.val (le_antisymm down up)
  obtain ⟨slots, valid, read⟩ := functionFromRelation RDef each
  exact ⟨slots, valid, fun x q pair => seq.znth_eq_of_mem ((read x q).mp pair).2.2.1⟩

/-- Internally coded elementarity suffices for the literal comparison
with the identity assignment. -/
theorem CodedElementary.generatedComparison {d j : V} (elementary : CodedElementary d j) :
    GeneratedComparison d j := by
  refine (generatedComparison_iff_identity d j).mpr ⟨elementary.1, fun R member before => ?_⟩
  obtain ⟨support, inTuples, compile⟩ := generated_representable member
  obtain ⟨supportSeq, finite, bound⟩ := (mem_tupleUniverse d support).mp inTuples
  obtain ⟨slots, slotsFn, slotsRead⟩ := support_slots supportSeq
  have empty : IsFormulaWord (∅ : V) := by simp [IsFormulaWord]
  obtain ⟨word,index,wf,within,arity,_,meaning⟩ := compile _ finite slots slotsFn ∅ empty
  obtain ⟨images,reads,boundedImages⟩ := readsTuple_exists elementary.1 supportSeq bound
  have tuple : Tuple d support (lh support) := ⟨supportSeq, rfl, bound⟩
  have imageTuple : Tuple d images (lh support) := ⟨reads.sequence, reads.length, boundedImages⟩
  have original : ReadsSlots (identity d) slots support := by
    intro x q entry
    exact (diagonal_at _ _ _).mpr ⟨bound x (mem_of_mem_functions slotsFn entry).1, slotsRead x q entry⟩
  have transported : ReadsSlots j slots images := by
    intro x q entry
    simpa only [slotsRead x q entry] using reads.each q (mem_of_mem_functions slotsFn entry).2
  have sat := (meaning (identity d) (identity_mem_universe d) support tuple original).mp before
  have satImages := (elementary.2 word wf index within support (arity.symm ▸ tuple) images reads).mp sat
  exact (meaning j elementary.1 images imageTuple transported).mpr satImages

end I0451.Logic.SetAssignments
