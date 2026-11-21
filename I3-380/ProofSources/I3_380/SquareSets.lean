module
public import I3_380.SquareParameters
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

/-- Separate a represented column from a set. -/
theorem separate_column (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (r : A) (input : Point) {b : Point} (hasName : S.Named b) :
    ∃ output, ∀ x, S.rel (M.constant .E) x output ↔
      S.rel (M.constant .E) x input ∧ S.rel r x b := by
  obtain ⟨name, describes⟩ := hasName
  let diagonal := domain M (M.product r name)
  have hDiagonal (x y : Point) : S.rel diagonal x y ↔ x = y ∧ S.rel r x b := by
    change S.rel (domain M (M.product r name)) x y ↔ _
    simp only [S.domain_iff, S.product, describes]
    constructor
    · rintro ⟨eq, _, c, edge, same, _⟩
      exact ⟨eq, same ▸ edge⟩
    · rintro ⟨eq, edge⟩
      exact ⟨eq, b, b, edge, rfl, rfl⟩
  obtain ⟨output, contents⟩ := S.exact_image_of_functional hM diagonal
    (fun x a b ha hb => ((hDiagonal x a).mp ha).1.symm.trans ((hDiagonal x b).mp hb).1) input
  refine ⟨output, fun x => (contents x).trans ?_⟩
  simp only [hDiagonal]
  constructor
  · rintro ⟨z, hz, same, relation⟩
    cases same
    exact ⟨hz, relation⟩
  · rintro ⟨inInput, relation⟩
    exact ⟨x, inInput, rfl, relation⟩

/-- Separation for first-order formulas, including extra represented relations. -/
theorem separation (P : QuasiProjections S) (hM : M.Models preceding)
    (allNamed : ∀ x, S.Named x) (params : List Point)
    (formula : RelationFormula A) (bound : formula.Bound (params.length + 2)) (input parameter : Point) :
    ∃ output, ∀ x, S.rel (M.constant .E) x output ↔
      S.rel (M.constant .E) x input ∧ RelationFormula.eval S formula (parameterEnv params x parameter) := by
  obtain ⟨r, rSpec⟩ := represented_binary P allNamed params formula bound
  obtain ⟨output, contents⟩ := S.separate_column hM r input (allNamed parameter)
  exact ⟨output, fun x => (contents x).trans (and_congr_right fun _ => rSpec x parameter)⟩

theorem powerset (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (allNamed : ∀ x, S.Named x)
    (pairs : ∀ a b, ∃ p, Logic.Internal.Pair (S.rel (M.constant .E)) a b p) (x : Point) :
    ∃ power, ∀ y, S.rel (M.constant .E) y power ↔
      ∀ z, S.rel (M.constant .E) z y → S.rel (M.constant .E) z x := by
  obtain ⟨singleton, hSingleton⟩ := pairs x x
  obtain ⟨cover, contains⟩ := S.power_cover hM singleton
  have xMem : S.rel (M.constant .E) x singleton := (hSingleton x).mpr (Or.inl rfl)
  obtain ⟨power, contents⟩ := S.separate_column hM (M.constant .T) cover (allNamed x)
  refine ⟨power, fun y => (contents y).trans ?_⟩
  exact ⟨fun h => (S.subset_iff hM y x).mp h.2,
    fun h => ⟨contains x y xMem ((S.subset_iff hM y x).mpr h), (S.subset_iff hM y x).mpr h⟩⟩

theorem union_set (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (allNamed : ∀ x, S.Named x)
    (pairs : ∀ a b, ∃ p, Logic.Internal.Pair (S.rel (M.constant .E)) a b p) (x : Point) :
    ∃ union, ∀ z, S.rel (M.constant .E) z union ↔
      ∃ y, S.rel (M.constant .E) y x ∧ S.rel (M.constant .E) z y := by
  let e := M.constant .E
  obtain ⟨cover, contains⟩ := S.power_cover hM x
  obtain ⟨image, imageSpec⟩ := S.exact_image hM (M.converse e) cover
  have containsUnion (z y : Point) (hy : S.rel e y x) (hz : S.rel e z y) : S.rel e z image := by
    obtain ⟨singleton, sing⟩ := pairs z z
    have bound : S.rel (M.constant .T) singleton y := (S.subset_iff hM singleton y).mpr fun t ht =>
      (((sing t).mp ht).elim id id).symm ▸ hz
    have inCover : S.rel e singleton cover := contains y singleton hy bound
    have unique (t : Point) : S.rel (M.converse e) singleton t ↔ t = z :=
      (S.converse _ _ _).trans ((sing t).trans ⟨fun h => h.elim id id, Or.inl⟩)
    exact (imageSpec z).mpr ⟨singleton, inCover, S.choice_on_single_row hM _ _ _ unique⟩
  obtain ⟨union, out⟩ := S.separate_column hM (M.product e e) image (allNamed x)
  refine ⟨union, fun z => ?_⟩
  rw [out, S.product]
  exact ⟨fun h => by obtain ⟨y, hy, hx⟩ := h.2; exact ⟨y, hx, hy⟩,
    fun ⟨y, hy, hz⟩ => ⟨containsUnion z y hy hz, y, hz, hy⟩⟩

end PalomarI3380.SquareRepresentation
