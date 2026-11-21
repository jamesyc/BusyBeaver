module
public import I0451.Logic.FormulaWordPrefix

/-! Constructors for extending a well-formed formula word, with the
satisfaction rule for each appended node. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure FormulaNodeAt (word index arity : V) : Prop where
  formed : IsFormulaWord word
  indexMem : index ∈ lh word
  arityEq : nodeArity word index = arity

theorem FormulaNodeAt.append_mem {word n x y : V} (old : IsFormulaWord word)
    (nNat : n ∈ (ω : V)) (hx : x ∈ n) (hy : y ∈ n) :
    FormulaNodeAt (word ⁀' nodeRecord n 0 x y) (lh word) n ∧
      ∀ {d args}, Tuple d args n →
        (Satisfies d (word ⁀' nodeRecord n 0 x y) (lh word) args ↔ znth args x ∈ znth args y) := by
  have fields := nodeRecord_fields (read_appended_node word (nodeRecord n 0 x y) old.1)
  have formed : IsFormulaNode (word ⁀' nodeRecord n 0 x y) (lh word) := by
    unfold IsFormulaNode
    rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]
    exact ⟨nNat, .inl ⟨rfl, hx, hy⟩⟩
  have good := old.append formed
  have here := appended_index (record := nodeRecord n 0 x y) old.1
  refine ⟨⟨good, here, fields.1⟩, fun tuple => ?_⟩
  apply Satisfies.leaf good here (fields.1.symm ▸ tuple)
  intro table
  rw [NodeSatisfies.atomic_mem fields.2.1, fields.2.2.1, fields.2.2.2]

theorem FormulaNodeAt.append_imp {word n x y : V}
    (left : FormulaNodeAt word x n) (right : FormulaNodeAt word y n) :
    FormulaNodeAt (word ⁀' nodeRecord n 3 x y) (lh word) n ∧
      ∀ {d args}, Tuple d args n →
        (Satisfies d (word ⁀' nodeRecord n 3 x y) (lh word) args ↔
          (Satisfies d word x args → Satisfies d word y args)) := by
  have old := left.formed
  have nNat : n ∈ (ω : V) := left.arityEq ▸ (old.2.2 x left.indexMem).1
  let record := nodeRecord n 3 x y
  have fields := nodeRecord_fields (read_appended_node word record old.1)
  have prefixProof := FormulaPrefix.append word record old.1
  have leftArity := (prefixProof.fields left.indexMem).1.trans left.arityEq
  have rightArity := (prefixProof.fields right.indexMem).1.trans right.arityEq
  have formed : IsFormulaNode (word ⁀' record) (lh word) := by
    unfold IsFormulaNode
    rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]
    exact ⟨nNat, .inr (.inr (.inr (.inl ⟨rfl, left.indexMem, right.indexMem, leftArity, rightArity⟩)))⟩
  have good := old.append formed
  have here := appended_index (record := record) old.1
  refine ⟨⟨good, here, fields.1⟩, fun tuple => ?_⟩
  have op := Satisfies.implication good here (fields.1.symm ▸ tuple) fields.2.1
  rw [fields.2.2.1, fields.2.2.2] at op
  exact op.trans ((prefixProof.satisfaction old good left.indexMem).symm.imp
    (prefixProof.satisfaction old good right.indexMem).symm)

theorem FormulaNodeAt.append_ex {word n x : V}
    (nNat : n ∈ (ω : V)) (body : FormulaNodeAt word x (succ n)) :
    FormulaNodeAt (word ⁀' nodeRecord n 4 x 0) (lh word) n ∧
      ∀ {d args}, Tuple d args n →
        (Satisfies d (word ⁀' nodeRecord n 4 x 0) (lh word) args ↔
          ∃ value ∈ d, Satisfies d word x (args ⁀' value)) := by
  have old := body.formed
  let record := nodeRecord n 4 x 0
  have fields := nodeRecord_fields (read_appended_node word record old.1)
  have prefixProof := FormulaPrefix.append word record old.1
  have bodyArity := (prefixProof.fields body.indexMem).1.trans body.arityEq
  have formed : IsFormulaNode (word ⁀' record) (lh word) := by
    unfold IsFormulaNode
    rw [fields.1, fields.2.1, fields.2.2.1]
    exact ⟨nNat, .inr (.inr (.inr (.inr (.inl ⟨rfl, body.indexMem, bodyArity⟩))))⟩
  have good := old.append formed
  have here := appended_index (record := record) old.1
  refine ⟨⟨good, here, fields.1⟩, fun tuple => ?_⟩
  have op := Satisfies.existential good here (fields.1.symm ▸ tuple) fields.2.1
  rw [fields.2.2.1] at op
  exact op.trans (exists_congr fun _ => and_congr_right fun _ =>
    (prefixProof.satisfaction old good body.indexMem).symm)

end I0451.Logic.SetFormulaPrograms
