module
public import I0451.Logic.NaturalBounds

/-! A set-coded first-order formula is a finite sequence of expression
nodes. A node records its parameter arity, its connective, and any
references to earlier nodes. The binder appends its variable to the
parameter tuple. Bounded existential quantification is a primitive
abbreviation with its bound in a parameter slot. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nodeArity (word index : V) : V := kpair.π₁ (znth word index)
noncomputable def nodeKind (word index : V) : V := kpair.π₁ (kpair.π₂ (znth word index))
noncomputable def firstOperand (word index : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ (znth word index)))
noncomputable def secondOperand (word index : V) : V := kpair.π₂ (kpair.π₂ (kpair.π₂ (znth word index)))

noncomputable def nodeRecord (arity kind left right : V) : V :=
  ⟨arity, ⟨kind, ⟨left, right⟩ₖ⟩ₖ⟩ₖ

theorem nodeRecord_fields {word i n tag x y : V} (encoded : znth word i = nodeRecord n tag x y) :
    nodeArity word i = n ∧ nodeKind word i = tag ∧ firstOperand word i = x ∧ secondOperand word i = y := by
  simp [nodeArity, nodeKind, firstOperand, secondOperand, encoded, nodeRecord]

def IsFormulaNode (word index : V) : Prop :=
  let n := nodeArity word index
  let kind := nodeKind word index
  let x := firstOperand word index
  let y := secondOperand word index
  n ∈ (ω : V) ∧
    (kind = 0 ∧ x ∈ n ∧ y ∈ n ∨
     kind = 1 ∧ x ∈ n ∧ y ∈ n ∨
     kind = 2 ∨
     kind = 3 ∧ x ∈ index ∧ y ∈ index ∧ nodeArity word x = n ∧ nodeArity word y = n ∨
     kind = 4 ∧ x ∈ index ∧ nodeArity word x = succ n ∨
     kind = 5 ∧ x ∈ index ∧ y ∈ n ∧ nodeArity word x = succ n)

def IsFormulaWord (word : V) : Prop :=
  Seq word ∧ lh word ∈ (ω : V) ∧ ∀ index ∈ lh word, IsFormulaNode word index

def Tuple (d args arity : V) : Prop :=
  Seq args ∧ lh args = arity ∧ range args ⊆ d

noncomputable def tupleUniverse (d : V) : V :=
  sep (℘ ((ω : V) ×ˢ d)) (fun args => Seq args ∧ lh args ∈ (ω : V)) (by definability)

theorem mem_tupleUniverse (d args : V) :
    args ∈ tupleUniverse d ↔ Seq args ∧ lh args ∈ (ω : V) ∧ range args ⊆ d := by
  rw [tupleUniverse, mem_sep_iff, mem_power_iff]
  constructor
  · rintro ⟨inside, seq, finite⟩
    refine ⟨seq, finite, fun x inRange => ?_⟩
    obtain ⟨i, read⟩ := mem_range_iff.mp inRange
    obtain ⟨i', _, x', insideD, eq⟩ := mem_prod_iff.mp (inside _ read)
    exact (kpair_inj eq).2.symm ▸ insideD
  · rintro ⟨seq, finite, bounded⟩
    refine ⟨fun p hp => ?_, seq, finite⟩
    let : IsFunction args := seq.IsFunction
    obtain ⟨i, x, rfl⟩ := IsFunction.mem_eq_kpair hp
    have iNat := (show IsTransitive (ω : V) from inferInstance).transitive _ finite _ (seq.lt_lh_of_mem hp)
    exact mem_prod_iff.mpr ⟨i, iNat, x, bounded _ (mem_range_iff.mpr ⟨i,hp⟩), rfl⟩

theorem Tuple.append {d args arity value : V} (tuple : Tuple d args arity) (hasValue : value ∈ d) :
    Tuple d (args ⁀' value) (succ arity) := by
  obtain ⟨sequence, length, bounds⟩ := tuple
  refine ⟨sequence.seqCons _, by rw [sequence.lh_seqCons, length], ?_⟩
  intro x found
  obtain ⟨i, entry⟩ := mem_range_iff.mp found
  rcases kpair_mem_seqCons_iff.mp entry with ⟨_, rfl⟩ | earlier
  · exact hasValue
  · exact bounds _ (mem_range_iff.mpr ⟨i,earlier⟩)

def finiteOrdinalDef : Nat → SetTheorySemisentence 1
  | 0 => isEmpty
  | n + 1 => “x. ∃ p, !(finiteOrdinalDef n) p ∧ !succ.dfn x p”

theorem finiteOrdinal_defined (n : Nat) :
    Defined (fun v : Fin 1 → V => v 0 = (n : V)) (finiteOrdinalDef n) := by
  induction n with
  | zero =>
    refine .mk fun v => ?_
    simpa [finiteOrdinalDef, isEmpty, FFL.FirstOrder.SetTheory.IsEmpty, zero_def] using
      (isEmpty_iff_eq_empty (x := v 0))
  | succ n ih =>
    refine .mk fun v => ?_
    simp [finiteOrdinalDef, ih.iff, succ.defined.iff, num_succ_def, Matrix.comp_vecCons', Function.comp_def]

def arityDef : SetTheorySemisentence 3 :=
  f“result word index. result = !kpair.π₁.dfn (!znth.dfn word index)”

def kindDef : SetTheorySemisentence 3 :=
  f“result word index. result = !kpair.π₁.dfn (!kpair.π₂.dfn (!znth.dfn word index))”

def firstDef : SetTheorySemisentence 3 :=
  f“result word index. result = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!znth.dfn word index)))”

def secondDef : SetTheorySemisentence 3 :=
  f“result word index. result = !kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!znth.dfn word index)))”

theorem arity_defines : DefinedFunction (fun v : Fin 2 → V => nodeArity (v 0) (v 1)) arityDef :=
  .mk fun v => by simp [arityDef, nodeArity, znth.defined.iff, kpair.π₁.defined.iff]

theorem kind_defines : DefinedFunction (fun v : Fin 2 → V => nodeKind (v 0) (v 1)) kindDef :=
  .mk fun v => by simp [kindDef, nodeKind, znth.defined.iff, kpair.π₁.defined.iff, kpair.π₂.defined.iff]

theorem first_defines : DefinedFunction (fun v : Fin 2 → V => firstOperand (v 0) (v 1)) firstDef :=
  .mk fun v => by simp [firstDef, firstOperand, znth.defined.iff, kpair.π₁.defined.iff, kpair.π₂.defined.iff]

theorem second_defines : DefinedFunction (fun v : Fin 2 → V => secondOperand (v 0) (v 1)) secondDef :=
  .mk fun v => by simp [secondDef, secondOperand, znth.defined.iff, kpair.π₂.defined.iff]

def formulaNodeDef : SetTheorySemisentence 2 :=
  “word index. ∃ n kind x y w,
     !arityDef n word index ∧ !kindDef kind word index ∧ !firstDef x word index ∧ !secondDef y word index ∧
     !isω w ∧ n ∈ w ∧
     ((!(finiteOrdinalDef 0) kind ∧ x ∈ n ∧ y ∈ n) ∨
      (!(finiteOrdinalDef 1) kind ∧ x ∈ n ∧ y ∈ n) ∨
      !(finiteOrdinalDef 2) kind ∨
      (!(finiteOrdinalDef 3) kind ∧ x ∈ index ∧ y ∈ index ∧ !arityDef n word x ∧ !arityDef n word y) ∨
      (!(finiteOrdinalDef 4) kind ∧ x ∈ index ∧ (∃ a, !succ.dfn a n ∧ !arityDef a word x)) ∨
      (!(finiteOrdinalDef 5) kind ∧ x ∈ index ∧ y ∈ n ∧ ∃ a, !succ.dfn a n ∧ !arityDef a word x))”

theorem formulaNode_defines : Defined (fun v : Fin 2 → V => IsFormulaNode (v 0) (v 1)) formulaNodeDef :=
  .mk fun v => by
    simp [formulaNodeDef, IsFormulaNode, arity_defines.iff, kind_defines.iff, first_defines.iff,
      second_defines.iff, (finiteOrdinal_defined (V := V) _).iff, succ.defined.iff, eq_comm]

def formulaWordDef : SetTheorySemisentence 1 :=
  “word. !seq.dfn word ∧ ∃ n w, !lh.dfn n word ∧ !isω w ∧ n ∈ w ∧ ∀ i ∈ n, !formulaNodeDef word i”

theorem formulaWord_defines : Defined (fun v : Fin 1 → V => IsFormulaWord (v 0)) formulaWordDef :=
  .mk fun v => by
    simp [formulaWordDef, IsFormulaWord, formulaNode_defines.iff, seq.defined.iff, lh.defined.iff]

theorem nodeArity_defined : ℒₛₑₜ-function₂[V] (nodeArity : V → V → V) :=
  arity_defines.to_definable

theorem nodeKind_defined : ℒₛₑₜ-function₂[V] (nodeKind : V → V → V) :=
  kind_defines.to_definable

theorem firstOperand_defined : ℒₛₑₜ-function₂[V] (firstOperand : V → V → V) :=
  first_defines.to_definable

theorem secondOperand_defined : ℒₛₑₜ-function₂[V] (secondOperand : V → V → V) :=
  second_defines.to_definable

def tupleDef : SetTheorySemisentence 3 :=
  f“d args arity. !seq.dfn args ∧ !lh.dfn arity args ∧ !range.dfn args ⊆ d”

theorem tuple_defines : Defined (fun v : Fin 3 → V => Tuple (v 0) (v 1) (v 2)) tupleDef :=
  .mk fun v => by simp [tupleDef, Tuple, seq.defined.iff, lh.defined.iff, range.defined.iff, eq_comm]

def tupleUniverseDef : SetTheorySemisentence 2 :=
  “d args. ∃ n w, !isω w ∧ n ∈ w ∧ !tupleDef d args n”

theorem tupleUniverse_defines : Defined (fun v : Fin 2 → V => v 1 ∈ tupleUniverse (v 0)) tupleUniverseDef :=
  .mk fun v => by simp [tupleUniverseDef, tuple_defines.iff, Tuple, mem_tupleUniverse, and_comm, and_assoc]

end I0451.Logic.SetFormulaPrograms
