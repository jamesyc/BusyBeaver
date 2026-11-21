module
public import I3_380.ClassAlgebra
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation

variable {V : Type}

/-- The expanded predicates may occur in a Separation or Replacement
instance. The unexpanded membership satisfies the ordinary axioms. -/
structure ClassAxioms (E G : V → V → Prop) : Prop where
  ordinary : ZFCModel E
  separation : ∀ r, Binary E G r → ∀ source anchor,
    ∃ output, ∀ x, E x output ↔ E x source ∧ r x anchor
  replacement : ∀ r, Binary E G r → (∀ x y z, r x y → r x z → y = z) → ∀ source,
    ∃ output, ∀ y, E y output ↔ ∃ x, E x source ∧ r x y

namespace ClassAxioms

variable {E G : V → V → Prop}

theorem from_ordinary (h : ZFCModel E) : ClassAxioms E (fun _ _ => False) :=
  ⟨h, fun _ defn => h.separation_binary defn, fun _ defn => h.replacement_binary defn⟩

noncomputable def context (h : ClassAxioms E G) (inhabited : Nonempty V) :
    SetContext (ClassRelation.algebra E G) V := by
  let p := Classical.choice inhabited
  let env := fun _ : Nat => p
  exact {
    square := ClassRelation.square E G
    inhabited := inhabited
    extensional := h.ordinary.extensional env
    emptySet := h.ordinary.empty env
    pairs := h.ordinary.pairing env
    powerSet := h.ordinary.power env
    unionSet := h.ordinary.union env
    subsetRel := fun _ _ => Iff.rfl
    choiceSet := h.ordinary.choice env
    separates := fun params phi scope => h.separation _ (ClassRelation.binary_class phi params p scope)
    replaces := fun params phi scope => h.replacement _ (ClassRelation.binary_class phi params p scope)
  }

end ClassAxioms

end PalomarI3380.Logic.Expanded
