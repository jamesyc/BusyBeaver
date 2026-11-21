module
public import I0451.Logic.SetSatisfaction

/-! Extending a formula word preserves its earlier syntax and truth
values. This supports a compositional compiler for parameter formulas. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure FormulaPrefix (first whole : V) : Prop where
  length : lh first ⊆ lh whole
  entries : ∀ i ∈ lh first, znth whole i = znth first i

theorem FormulaPrefix.refl (word : V) : FormulaPrefix word word :=
  ⟨subset_refl _, fun _ _ => rfl⟩

theorem FormulaPrefix.trans {a b c : V} (ab : FormulaPrefix a b) (bc : FormulaPrefix b c) :
    FormulaPrefix a c :=
  ⟨subset_trans ab.length bc.length, fun i hi => (bc.entries i (ab.length i hi)).trans (ab.entries i hi)⟩

theorem FormulaPrefix.append (word record : V) (seq : Seq word) : FormulaPrefix word (word ⁀' record) := by
  constructor
  · rw [seq.lh_seqCons]
    exact fun i inside => mem_succ_iff.mpr (.inr inside)
  · intro i inside
    exact (seq.seqCons record).znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt inside).mpr (seq.znth inside))

theorem FormulaPrefix.fields {a b i : V} (front : FormulaPrefix a b) (inside : i ∈ lh a) :
    nodeArity b i = nodeArity a i ∧ nodeKind b i = nodeKind a i ∧
      firstOperand b i = firstOperand a i ∧ secondOperand b i = secondOperand a i := by
  simp [nodeArity, nodeKind, firstOperand, secondOperand, front.entries i inside]

theorem FormulaPrefix.transfersNode {a b i : V} (front : FormulaPrefix a b) (inside : i ∈ lh a)
    (formed : IsFormulaNode a i) : IsFormulaNode b i := by
  obtain ⟨arity, tag, x, y⟩ := front.fields inside
  let ordinal : IsOrdinal (lh a) := isOrdinal_lh _
  have prior (j : V) (earlier : j ∈ i) : nodeArity b j = nodeArity a j :=
    (front.fields (ordinal.toIsTransitive.transitive _ inside _ earlier)).1
  unfold IsFormulaNode
  rw [arity, tag, x, y]
  refine ⟨formed.1, ?_⟩
  rcases formed.2 with atom | eq | falsity | ⟨imp, left, right, leftArity, rightArity⟩ |
    ⟨ex, left, leftArity⟩ | ⟨bounded, left, right, leftArity⟩
  · exact .inl atom
  · exact .inr (.inl eq)
  · exact .inr (.inr (.inl falsity))
  · exact .inr (.inr (.inr (.inl ⟨imp, left, right,
      (prior _ left).trans leftArity, (prior _ right).trans rightArity⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨ex, left, (prior _ left).trans leftArity⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨bounded, left, right, (prior _ left).trans leftArity⟩))))

theorem IsFormulaWord.append {word record : V} (old : IsFormulaWord word)
    (next : IsFormulaNode (word ⁀' record) (lh word)) : IsFormulaWord (word ⁀' record) := by
  refine ⟨old.1.seqCons _, by rw [old.1.lh_seqCons]; exact ω_succ_closed old.2.1,
    fun i inside => ?_⟩
  rw [old.1.lh_seqCons] at inside
  rcases mem_succ_iff.mp inside with same | earlier
  · exact same.symm ▸ next
  · exact (FormulaPrefix.append word record old.1).transfersNode earlier (old.2.2 i earlier)

theorem FormulaPrefix.satisfaction {d before after i args : V} (front : FormulaPrefix before after)
    (oldWf : IsFormulaWord before) (newWf : IsFormulaWord after) (inside : i ∈ lh before) :
    Satisfies d before i args ↔ Satisfies d after i args := by
  obtain ⟨running, grown⟩ := evaluation_exists d newWf
  let shortened := running ↾ (lh before)
  let : IsOrdinal (lh before) := isOrdinal_lh _
  have splitLength : lh before ⊆ lh running := grown.length.symm ▸ front.length
  have ss : Seq shortened := grown.sequence.restrict splitLength
  have reads (j : V) (inPrefix : j ∈ lh before) : znth shortened j = znth running j := by
    have read := grown.sequence.znth (splitLength j inPrefix)
    exact ss.znth_eq_of_mem (kpair_mem_restrict_iff.mpr ⟨read, inPrefix⟩)
  have prefixEvaluation : EvaluationPrefix d before (lh before) shortened := by
    refine ⟨ss, grown.sequence.lh_restrict splitLength, fun j inPrefix params => ?_⟩
    obtain ⟨arity, kind, left, right⟩ := front.fields inPrefix
    have earlier (k : V) (kBefore : k ∈ j) : znth shortened k = znth running k :=
      reads k ((show IsOrdinal (lh before) from inferInstance).toIsTransitive.transitive j inPrefix k kBefore)
    have keep := NodeSatisfies.congr (d := d) (oldWf.2.2 j inPrefix) earlier (args := params)
    have same : NodeSatisfies d after j running params ↔ NodeSatisfies d before j running params := by
      simp only [NodeSatisfies, kind, left, right]
    rw [reads j inPrefix, grown.evaluates j (front.length j inPrefix), arity, same, ← keep]
  rw [Satisfies.iff_mem oldWf prefixEvaluation, Satisfies.iff_mem newWf grown, reads i inside]

theorem read_appended_node (word record : V) (seq : Seq word) :
    znth (word ⁀' record) (lh word) = record :=
  (seq.seqCons record).znth_eq_of_mem (Seq.mem_seqCons word record)

theorem appended_index {word record : V} (seq : Seq word) :
    lh word ∈ lh (word ⁀' record) := by
  rw [seq.lh_seqCons]
  exact mem_succ_self _

end I0451.Logic.SetFormulaPrograms
