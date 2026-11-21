module
public import I3_380.SquareStages
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A}

theorem every_named (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (p : {x : Point // S.Named x}) : (S.namedSquare hM).Named p := by
  obtain ⟨name, hx⟩ := p.property
  refine ⟨name, fun a b => ?_⟩
  exact (hx a.val b.val).trans (by simp only [Subtype.ext_iff])

def join (M : Algebra A) (a b : A) : A :=
  M.nand (M.neg a) (M.neg b)

theorem join_iff (S : SquareRepresentation M Point) (a b : A) (x y : Point) :
    S.rel (join M a b) x y ↔ S.rel a x y ∨ S.rel b x y := by
  classical
  rw [join, S.nand, S.complement, S.complement]
  by_cases ha : S.rel a x y <;> by_cases hb : S.rel b x y <;> simp [ha, hb]

/-- Every point has a singleton, once a set with a member is available. -/
theorem singleton_of_named (S : SquareRepresentation M Point) (hM : M.Models preceding)
    {p : Point} (nameP : S.Named p) {w input : Point} (element : S.rel (M.constant .E) w input) :
    ∃ output, ∀ x, S.rel (M.constant .E) x output ↔ x = p := by
  obtain ⟨name, hName⟩ := nameP
  let graph := M.product (M.constant .U) name
  have value (a b : Point) : S.rel graph a b ↔ b = p := by
    change S.rel (M.product (M.constant .U) name) a b ↔ b = p
    simp only [S.product, S.universal, true_and, hName]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨p, rfl, h⟩⟩
  obtain ⟨output, hOut⟩ := S.exact_image_of_functional hM graph
    (fun a b c h₁ h₂ => ((value a b).mp h₁).trans ((value a c).mp h₂).symm) input
  refine ⟨output, fun x => ?_⟩
  simp only [hOut, value]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨w, element, h⟩⟩

/-- In the named hull the cover and image equations yield unordered pairs
before invoking any general instance of Separation or Replacement. -/
theorem unordered_pairs (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (allNamed : ∀ x, S.Named x) {seed seedSet : Point}
    (element : S.rel (M.constant .E) seed seedSet) (a b : Point) :
    ∃ pair, ∀ x, S.rel (M.constant .E) x pair ↔ x = a ∨ x = b := by
  classical
  obtain ⟨empty, noMembers⟩ := S.exists_empty hM a
  obtain ⟨singleton, singletonDef⟩ := S.singleton_of_named hM (allNamed empty) element
  obtain ⟨double, doubleDef⟩ := S.singleton_of_named hM (allNamed singleton) element
  have eInS : S.rel (M.constant .E) empty singleton := (singletonDef empty).mpr rfl
  have distinct : singleton ≠ empty := by
    intro eq
    exact noMembers empty (eq ▸ eInS)
  obtain ⟨cover, contains⟩ := S.power_cover hM double
  have sInD : S.rel (M.constant .E) singleton double := (doubleDef singleton).mpr rfl
  have eInC : S.rel (M.constant .E) empty cover := contains singleton empty sInD
    ((S.subset_iff hM empty singleton).mpr fun x h => (noMembers x h).elim)
  have sInC : S.rel (M.constant .E) singleton cover := contains singleton singleton sInD
    ((S.subset_iff hM singleton singleton).mpr fun _ h => h)
  obtain ⟨de, he⟩ := allNamed empty
  obtain ⟨da, ha⟩ := allNamed a
  obtain ⟨db, hb⟩ := allNamed b
  let other := M.neg (M.nand (M.constant .I) (M.neg de))
  let graph := join M (M.product (M.product de (M.constant .U)) da)
    (M.product (M.product other (M.constant .U)) db)
  have value (x y : Point) : S.rel graph x y ↔
      (x = empty ∧ y = a) ∨ (x ≠ empty ∧ y = b) := by
    simp only [graph, other, S.join_iff, S.product, S.universal, S.meet, S.complement, S.identity,
      he, ha, hb, and_true]
    constructor
    · rintro (⟨_, ⟨_, xe, _⟩, _, ya⟩ | ⟨_, ⟨_, same, nEmpty⟩, _, yb⟩)
      · exact Or.inl ⟨xe, ya⟩
      · cases same
        exact Or.inr ⟨fun h => nEmpty ⟨h, h⟩, yb⟩
    · rintro (⟨xEmpty, yA⟩ | ⟨hne, yB⟩)
      · exact Or.inl ⟨a, ⟨empty, xEmpty, rfl⟩, rfl, yA⟩
      · exact Or.inr ⟨b, ⟨x, rfl, fun eq => hne eq.1⟩, rfl, yB⟩
  have functional (x y z : Point) (hy : S.rel graph x y) (hz : S.rel graph x z) : y = z := by
    rcases (value x y).mp hy with ⟨h, rfl⟩ | ⟨hne, rfl⟩ <;>
      rcases (value x z).mp hz with ⟨h', rfl⟩ | ⟨hne', rfl⟩
    · rfl
    · exact (hne' h).elim
    · exact (hne h').elim
    · rfl
  obtain ⟨pair, hPair⟩ := S.exact_image_of_functional hM graph functional cover
  refine ⟨pair, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨origin, _, hr⟩ := (hPair x).mp hx
    exact ((value origin x).mp hr).elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  · rintro (eq | eq)
    · exact (hPair x).mpr ⟨empty, eInC, (value empty x).mpr (Or.inl ⟨rfl, eq⟩)⟩
    · exact (hPair x).mpr ⟨singleton, sInC, (value singleton x).mpr (Or.inr ⟨distinct, eq⟩)⟩

theorem named_hull_pairs (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (sep : ¬ ∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y)
    (a b : {x : Point // S.Named x}) :
    ∃ pair, ∀ x, (S.namedSquare hM).rel (M.constant .E) x pair ↔ x = a ∨ x = b := by
  obtain ⟨x, y, hx, hy, jxy, _⟩ := S.named_moved hM sep
  let V := S.namedSquare hM
  have diagonal : V.rel (M.constant .D) ⟨x, hx⟩ ⟨x, hx⟩ :=
    (V.domain_eq hM _ _).mpr ⟨rfl, ⟨y, hy⟩, jxy⟩
  obtain ⟨seedSet, hSeed⟩ := V.inhabited_set_of_domain hM diagonal
  exact V.unordered_pairs hM (S.every_named hM) hSeed a b

end PalomarI3380.SquareRepresentation
