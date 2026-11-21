module
public import I0451.Logic.FormulaArguments
public import I0451.Logic.FormulaWordConstructors
public import I0451.Logic.CodedElementarity
public import I0451.Logic.ElementarySets

/-! Encode ordinary finite first-order formulas as set-model formula
words. This links the internal elementarity criterion to the finite
formulas used to name parameters and prove rank preservation. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.SetAssignments I0451.Logic.ZFModel

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

structure EncodedFormula {n : Nat} (formula : Identity.Formula n) (before word index : V) : Prop where
  formed : IsFormulaWord word
  earlierWord : FormulaPrefix before word
  indexMem : index ∈ lh word
  arity : nodeArity word index = (n : V)
  evaluates : ∀ {d args : V} {v : Fin n → Domain E d}, MatchesArguments args v →
    (Satisfies d word index args ↔ formula.eval (domainMem d) v)

private theorem encode_mem {n : Nat} (x y : Fin n) (before : V) (old : IsFormulaWord before) :
    ∃ word index, EncodedFormula (.mem x y) before word index := by
  let record := nodeRecord (n : V) 0 (x.rev.val : V) (y.rev.val : V)
  obtain ⟨entry, semantics⟩ := FormulaNodeAt.append_mem old (ofNat_mem_ω n)
    (ofNat_mem_of_lt x.rev.isLt) (ofNat_mem_of_lt y.rev.isLt)
  refine ⟨before ⁀' record, lh before, entry.formed, FormulaPrefix.append _ _ old.1,
    entry.indexMem, entry.arityEq, ?_⟩
  intro d args values assignment
  rw [semantics assignment.tuple, assignment.reads x, assignment.reads y]
  rfl

private theorem encode_eq {n : Nat} (x y : Fin n) (before : V) (old : IsFormulaWord before) :
    ∃ word index, EncodedFormula (.eq x y) before word index := by
  let record := nodeRecord (n : V) 1 (x.rev.val : V) (y.rev.val : V)
  let word := before ⁀' record
  have fields := nodeRecord_fields (read_appended_node before record old.1)
  have formed : IsFormulaNode word (lh before) := by
    unfold IsFormulaNode
    rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]
    exact ⟨ofNat_mem_ω _, .inr (.inl ⟨rfl, ofNat_mem_of_lt x.rev.isLt, ofNat_mem_of_lt y.rev.isLt⟩)⟩
  have good := old.append formed
  have hit := appended_index (record := record) old.1
  refine ⟨word, lh before, good, FormulaPrefix.append _ _ old.1, hit, fields.1, ?_⟩
  intro d args values assignment
  apply Satisfies.leaf good hit (fields.1.symm ▸ assignment.tuple)
  intro table
  rw [NodeSatisfies.atomic_eq fields.2.1, fields.2.2.1, fields.2.2.2, assignment.reads x, assignment.reads y]
  exact Subtype.ext_iff.symm

private theorem encode_false (n : Nat) (before : V) (old : IsFormulaWord before) :
    ∃ word index, EncodedFormula (.bot (n := n)) before word index := by
  let record := nodeRecord (n : V) 2 0 0
  let word := before ⁀' record
  have fields := nodeRecord_fields (read_appended_node before record old.1)
  have formed : IsFormulaNode word (lh before) := by
    unfold IsFormulaNode
    rw [fields.1, fields.2.1]
    exact ⟨ofNat_mem_ω _, .inr (.inr (.inl rfl))⟩
  have good := old.append formed
  have hit := appended_index (record := record) old.1
  refine ⟨word, lh before, good, FormulaPrefix.append _ _ old.1, hit, fields.1, ?_⟩
  intro d args values assignment
  exact Satisfies.leaf good hit (fields.1.symm ▸ assignment.tuple)
    (fun _ => NodeSatisfies.falsity fields.2.1)

theorem encode_finite_formula {n : Nat} (formula : Identity.Formula n) (before : V) (old : IsFormulaWord before) :
    ∃ word index, EncodedFormula formula before word index := by
  induction formula generalizing before with
  | mem x y => exact encode_mem x y before old
  | eq x y => exact encode_eq x y before old
  | bot => exact encode_false _ before old
  | @imp n a b encodeA encodeB =>
    obtain ⟨aWord, ai, ac⟩ := encodeA before old
    obtain ⟨bWord, bi, bc⟩ := encodeB aWord ac.formed
    let record := nodeRecord (n : V) 3 ai bi
    have left : FormulaNodeAt bWord ai (n : V) :=
      ⟨bc.formed, bc.earlierWord.length ai ac.indexMem,
        (bc.earlierWord.fields ac.indexMem).1.trans ac.arity⟩
    obtain ⟨entry, semantics⟩ :=
      FormulaNodeAt.append_imp left ⟨bc.formed, bc.indexMem, bc.arity⟩
    have keeps := FormulaPrefix.append bWord record bc.formed.1
    refine ⟨bWord ⁀' record, lh bWord, entry.formed,
      ac.earlierWord.trans (bc.earlierWord.trans keeps), entry.indexMem, entry.arityEq, ?_⟩
    intro d args values assignment
    have leftSat := (bc.earlierWord.satisfaction ac.formed bc.formed ac.indexMem).symm.trans
      (ac.evaluates assignment)
    exact (semantics assignment.tuple).trans (leftSat.imp (bc.evaluates assignment))
  | @ex n body encodeBody =>
    obtain ⟨inner, oldIndex, prior⟩ := encodeBody before old
    let record := nodeRecord (n : V) 4 oldIndex 0
    obtain ⟨entry, semantics⟩ := FormulaNodeAt.append_ex (ofNat_mem_ω n)
      ⟨prior.formed, prior.indexMem, prior.arity.trans (num_succ_def n)⟩
    have keeps := FormulaPrefix.append inner record prior.formed.1
    refine ⟨inner ⁀' record, lh inner, entry.formed, prior.earlierWord.trans keeps,
      entry.indexMem, entry.arityEq, ?_⟩
    intro d args values assignment
    rw [semantics assignment.tuple]
    have bodyAnswer (u : Domain E d) :
        Satisfies d inner oldIndex (args ⁀' u.val) ↔ body.eval (domainMem d) (Fin.cases u values) :=
      prior.evaluates (assignment.append u)
    exact ⟨fun ⟨x, hx, checked⟩ => ⟨⟨x,hx⟩, (bodyAnswer ⟨x,hx⟩).mp checked⟩,
      fun ⟨x, checked⟩ => ⟨x.val, x.property, (bodyAnswer x).mpr checked⟩⟩

theorem _root_.I0451.Logic.SetAssignments.CodedElementary.decoded_elementary {d code : V}
    (coded : CodedElementary d code) :
    ∃ f : Domain E d → Domain E d, Encodes E d code f ∧ Identity.Elementary (domainMem d) f := by
  obtain ⟨f, reads⟩ := (is_map_iff_encodes ZFModel.setOperations).mp ((mem_universe d code).mp coded.1)
  refine ⟨f, reads, fun formula values => ?_⟩
  have empty : IsFormulaWord (∅ : V) := by simp [IsFormulaWord]
  obtain ⟨word, index, syntaxCode⟩ := encode_finite_formula formula ∅ empty
  obtain ⟨args, assignment⟩ := matching_arguments_exist values
  obtain ⟨images, matchesImages⟩ := matching_arguments_exist (f ∘ values)
  have law := coded.2 word syntaxCode.formed index syntaxCode.indexMem args
    (syntaxCode.arity.symm ▸ assignment.tuple) images (assignment.readsTuple reads matchesImages)
  exact (syntaxCode.evaluates assignment).symm.trans (law.trans (syntaxCode.evaluates matchesImages))

end I0451.Logic.SetFormulaPrograms
