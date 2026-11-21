module
public import I3_380.SquarePairs
public import I3_380.Logic.History
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A}

structure QuasiProjections (S : SquareRepresentation M Point) where
  first : A
  second : A
  firstFunction : ∀ p a b, S.rel first p a → S.rel first p b → a = b
  secondFunction : ∀ p a b, S.rel second p a → S.rel second p b → a = b
  pair : ∀ a b, ∃ p, S.rel first p a ∧ S.rel second p b

theorem choice_on_single_row (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (r : A) (p a : Point) (unique : ∀ x, S.rel r p x ↔ x = a) :
    S.rel (M.choice r) p a := by
  obtain ⟨x, hx⟩ := (S.choice_domain hM r p).mpr ⟨a, (unique a).mpr rfl⟩
  exact (unique x).mp (S.choice_sub hM r hx) ▸ hx

/-- Obtain the two projections from a Kuratowski code. Selection makes
them single-valued on every input, while the indicated rows already have
exactly one possible value at every actual pair code. -/
theorem projections_of_selection (S : SquareRepresentation M Point)
    (pairs : ∀ a b, ∃ p, Logic.Internal.Pair (S.rel (M.constant .E)) a b p)
    (select : A → A)
    (functional : ∀ r p x y, S.rel (select r) p x → S.rel (select r) p y → x = y)
    (single : ∀ r p a, (∀ x, S.rel r p x ↔ x = a) → S.rel (select r) p a) :
    Nonempty (QuasiProjections S) := by
  classical
  let member := S.rel (M.constant .E)
  let reverse := M.converse (M.constant .E)
  let common := M.neg (M.product reverse (M.neg reverse))
  let union := M.product reverse reverse
  let extra := M.neg (M.nand union (M.neg common))
  let emptyExtra := M.neg (M.nand (M.constant .I) (M.neg (domain M extra)))
  let second := join M extra (M.product emptyExtra common)
  have common_def (p x : Point) :
      S.rel common p x ↔ ∀ set, member set p → member x set := by
    change S.rel (M.neg (M.product (M.converse (M.constant .E))
      (M.neg (M.converse (M.constant .E))))) p x ↔ _
    simp only [S.complement, S.product, S.converse, member]
    constructor
    · intro no set inPair
      exact Classical.byContradiction fun missing => no ⟨set, inPair, missing⟩
    · rintro every ⟨set, inPair, missing⟩
      exact missing (every set inPair)
  have union_def (p x : Point) : S.rel union p x ↔ ∃ set, member set p ∧ member x set := by
    change S.rel (M.product (M.converse (M.constant .E)) (M.converse (M.constant .E))) p x ↔ _
    simp only [S.product, S.converse, member]
  have extra_def (p x : Point) : S.rel extra p x ↔ S.rel union p x ∧ ¬S.rel common p x := by
    simp only [extra, S.meet, S.complement]
  have other_def (p x : Point) :
      S.rel second p x ↔ S.rel extra p x ∨ ((¬ ∃ y, S.rel extra p y) ∧ S.rel common p x) := by
    change S.rel (join M extra (M.product emptyExtra common)) p x ↔ _
    rw [S.join_iff, S.product]
    simp only [emptyExtra, S.meet, S.identity, S.complement, S.domain_iff]
    constructor
    · rintro (h | ⟨q, ⟨eq, no⟩, xIn⟩)
      · exact Or.inl h
      · subst q
        exact Or.inr ⟨fun h => no ⟨rfl, h⟩, xIn⟩
    · rintro (h | ⟨no, commonValue⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, ⟨rfl, fun h => no h.2⟩, commonValue⟩
  refine ⟨⟨select common, select second, functional common, functional second, ?_⟩⟩
  intro a b
  obtain ⟨singleSet, hSingle⟩ := pairs a a
  obtain ⟨double, hDouble⟩ := pairs a b
  obtain ⟨code, hPair⟩ := pairs singleSet double
  have common_row (x : Point) : S.rel common code x ↔ x = a := by
    rw [common_def]
    constructor
    · intro commonValues
      exact ((hSingle x).mp (commonValues singleSet ((hPair singleSet).mpr (Or.inl rfl)))).elim id id
    · intro eq
      subst x
      intro y memberY
      rcases (hPair y).mp memberY with rfl | rfl
      · exact (hSingle a).mpr (Or.inl rfl)
      · exact (hDouble a).mpr (Or.inl rfl)
  have union_row (x : Point) : S.rel union code x ↔ x = a ∨ x = b := by
    rw [union_def]
    constructor
    · rintro ⟨y, hy, hx⟩
      rcases (hPair y).mp hy with rfl | rfl
      · exact Or.inl (((hSingle x).mp hx).elim id id)
      · exact (hDouble x).mp hx
    · intro eq
      exact ⟨double, (hPair double).mpr (Or.inr rfl), (hDouble x).mpr eq⟩
  have extra_row (x : Point) : S.rel extra code x ↔ (x = a ∨ x = b) ∧ x ≠ a := by
    simp only [extra_def, union_row, common_row]
  have second_row (x : Point) : S.rel second code x ↔ x = b := by
    rw [other_def, extra_row, common_row]
    by_cases eq : b = a
    · subst b
      have no : ¬∃ y, S.rel extra code y := by
        rintro ⟨y, he⟩
        obtain ⟨same, ne⟩ := (extra_row y).mp he
        exact ne (same.elim id id)
      simp [no]
    · have hB : S.rel extra code b := (extra_row b).mpr ⟨Or.inr rfl, eq⟩
      constructor
      · rintro (⟨h, ne⟩ | ⟨no, _⟩)
        · exact h.elim (fun same => (ne same).elim) id
        · exact (no ⟨b, hB⟩).elim
      · intro h
        exact Or.inl ⟨Or.inr h, fun ha => eq (h.symm.trans ha)⟩
  exact ⟨code, single common code a common_row, single second code b second_row⟩

theorem quasi_projections (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (pairs : ∀ a b, ∃ p, Logic.Internal.Pair (S.rel (M.constant .E)) a b p) :
    Nonempty (QuasiProjections S) :=
  S.projections_of_selection pairs M.choice (fun r _ _ _ => S.choice_functional hM r)
    (S.choice_on_single_row hM)

theorem named_hull_projections (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (sep : ¬ ∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y) :
    Nonempty (QuasiProjections (S.namedSquare hM)) :=
  (S.namedSquare hM).quasi_projections hM (S.named_hull_pairs hM sep)

end PalomarI3380.SquareRepresentation
