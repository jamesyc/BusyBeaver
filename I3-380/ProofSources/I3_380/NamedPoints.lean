module
public import I3_380.Square
@[expose] public section

namespace PalomarI3380.SquareRepresentation

variable {A Point : Type} {M : Algebra A}

/-- An algebra element names a point when its projection is exactly the
diagonal of the singleton containing that point. -/
def Named (S : SquareRepresentation M Point) (p : Point) : Prop :=
  ∃ diagonal, ∀ x y, S.rel diagonal x y ↔ x = p ∧ y = p

def domain (M : Algebra A) (r : A) : A :=
  M.neg (M.nand (M.constant .I) (M.product r (M.constant .U)))

theorem domain_iff (S : SquareRepresentation M Point) (r : A) (x y : Point) :
    S.rel (domain M r) x y ↔ x = y ∧ ∃ z, S.rel r x z := by
  simp only [domain, S.meet, S.identity, S.product, S.universal, and_true]

theorem named_empty (S : SquareRepresentation M Point) (hM : M.Models Manifest.preceding)
    (x : Point) : ∃ p, S.Named p ∧ ∀ z, ¬ S.rel (M.constant .E) z p := by
  obtain ⟨p, empty⟩ := S.exists_empty hM x
  let members := M.converse (M.constant .E)
  let d := M.neg (M.nand (M.constant .I) (M.neg (M.product members (M.constant .U))))
  refine ⟨p, ⟨d, ?_⟩, empty⟩
  intro a b
  change S.rel (M.neg (M.nand (M.constant .I)
    (M.neg (M.product (M.converse (M.constant .E)) (M.constant .U))))) a b ↔ _
  simp only [S.meet, S.identity, S.complement, S.product, S.universal, and_true, S.converse]
  constructor
  · rintro ⟨rfl, h⟩
    have ha : a = p := S.extensional hM (fun z =>
      ⟨fun hz => (h ⟨z, hz⟩).elim, fun hz => (empty z hz).elim⟩)
    exact ⟨ha, ha⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, fun ⟨z, hz⟩ => empty z hz⟩

/-- Every nonempty represented subidentity contains a named point. -/
theorem named_of_subidentity (S : SquareRepresentation M Point)
    (hM : M.Models Manifest.preceding) (r : A)
    (diagonal : ∀ x y, S.rel r x y → x = y) {x : Point} (hx : S.rel r x x) :
    ∃ y, S.Named y ∧ S.rel r y y := by
  obtain ⟨start, ⟨startName, hStart⟩, _⟩ := S.named_empty hM x
  let allToR := M.product (M.constant .U) r
  have hAll : S.rel allToR start x :=
    (S.product _ _ _ _).mpr ⟨x, (S.universal _ _).mpr trivial, hx⟩
  obtain ⟨y, hy⟩ := (S.choice_domain hM allToR start).mpr ⟨x, hAll⟩
  obtain ⟨z, _, hz⟩ := (S.product _ _ _ _).mp (S.choice_sub hM allToR hy)
  have onDiagonal : S.rel r y y := diagonal z y hz ▸ hz
  let name := domain M (M.converse (M.product startName (M.choice allToR)))
  refine ⟨y, ⟨name, ?_⟩, onDiagonal⟩
  intro a b
  change S.rel (domain M (M.converse (M.product startName (M.choice allToR)))) a b ↔ _
  simp only [S.domain_iff, S.converse, S.product, hStart]
  constructor
  · rintro ⟨rfl, _, _, ⟨rfl, rfl⟩, h⟩
    have ha : a = y := S.choice_functional hM allToR h hy
    exact ⟨ha, ha⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, start, start, ⟨rfl, rfl⟩, hy⟩

/-- Composition between named endpoints can be witnessed by a named
intermediate point. This is the composition step in restricting the
square to its named-point hull. -/
theorem composition_named (S : SquareRepresentation M Point) (hM : M.Models Manifest.preceding)
    (r s : A) {x y : Point} (hx : S.Named x) (hy : S.Named y) :
    S.rel (M.product r s) x y ↔ ∃ z, S.Named z ∧ S.rel r x z ∧ S.rel s z y := by
  obtain ⟨nameX, hNameX⟩ := hx
  obtain ⟨nameY, hNameY⟩ := hy
  let incoming := domain M (M.converse (M.product nameX r))
  let outgoing := domain M (M.product s nameY)
  let intermediate := M.neg (M.nand incoming outgoing)
  have hIntermediate (a b : Point) :
      S.rel intermediate a b ↔ a = b ∧ S.rel r x a ∧ S.rel s a y := by
    change S.rel (M.neg (M.nand
      (domain M (M.converse (M.product nameX r))) (domain M (M.product s nameY)))) a b ↔ _
    simp only [S.meet, S.domain_iff, S.converse, S.product, hNameX, hNameY]
    constructor
    · rintro ⟨⟨e, _, _, ⟨_, rfl⟩, hr⟩, ⟨_, _, _, hs, rfl, _⟩⟩
      exact ⟨e, hr, hs⟩
    · rintro ⟨rfl, hr, hs⟩
      exact ⟨⟨rfl, x, x, ⟨rfl, rfl⟩, hr⟩, ⟨rfl, y, y, hs, rfl, rfl⟩⟩
  rw [S.product]
  constructor
  · rintro ⟨z, hr, hs⟩
    have hdiag (a b : Point) (h : S.rel intermediate a b) := (hIntermediate a b).mp h |>.1
    obtain ⟨w, hw, hi⟩ := S.named_of_subidentity hM intermediate hdiag
      ((hIntermediate z z).mpr ⟨rfl, hr, hs⟩)
    exact ⟨w, hw, ((hIntermediate w w).mp hi).2⟩
  · rintro ⟨z, _, hr, hs⟩
    exact ⟨z, hr, hs⟩

/-- Restriction to named points still represents the relation-algebra reduct. -/
def namedSquare (S : SquareRepresentation M Point) (hM : M.Models Manifest.preceding) :
    SquareRepresentation M {p : Point // S.Named p} where
  rel a x y := S.rel a x.val y.val
  complement a x y := S.complement a x.val y.val
  converse a x y := S.converse a x.val y.val
  nand a b x y := S.nand a b x.val y.val
  universal x y := S.universal x.val y.val
  identity x y := (S.identity x.val y.val).trans Subtype.ext_iff.symm
  product a b x y := by
    rw [S.composition_named hM a b x.property y.property]
    exact ⟨fun ⟨z, hz, ha, hb⟩ => ⟨⟨z, hz⟩, ha, hb⟩,
      fun ⟨z, ha, hb⟩ => ⟨z.val, z.property, ha, hb⟩⟩

end PalomarI3380.SquareRepresentation
