module
public import I3_380.Conservativity
@[expose] public section

namespace PalomarI3380

/-- A single square component of a representation of the relation-algebra
reduct. The map need not preserve an operation induced by `choice`,
`localRel`, or `node` on the square. -/
structure SquareRepresentation {A : Type} (M : Algebra A) (Point : Type) where
  rel : A → Point → Point → Prop
  complement : ∀ a x y, rel (M.neg a) x y ↔ ¬ rel a x y
  converse : ∀ a x y, rel (M.converse a) x y ↔ rel a y x
  nand : ∀ a b x y, rel (M.nand a b) x y ↔ ¬ (rel a x y ∧ rel b x y)
  product : ∀ a b x y, rel (M.product a b) x y ↔ ∃ z, rel a x z ∧ rel b z y
  universal : ∀ x y, rel (M.constant .U) x y ↔ True
  identity : ∀ x y, rel (M.constant .I) x y ↔ x = y

namespace SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A}

theorem meet (S : SquareRepresentation M Point) (a b : A) (x y : Point) :
    S.rel (M.neg (M.nand a b)) x y ↔ S.rel a x y ∧ S.rel b x y := by
  classical
  rw [S.complement, S.nand]
  exact ⟨Classical.byContradiction, fun h hne => hne h⟩

private theorem choiceSub_mem : choiceSub ∈ preceding := by
  simp [preceding, retained]

private theorem choiceFunctional_mem : choiceFunctional ∈ preceding := by
  simp [preceding, retained]

private theorem choiceDomain_mem : choiceDomain ∈ preceding := by
  simp [preceding, retained]

private theorem image_mem : imageEquation ∈ preceding := by
  simp [preceding, retained]

theorem choice_sub (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (a : A) {x y : Point} (h : S.rel (M.choice a) x y) : S.rel a x y := by
  have equation := hM choiceSub choiceSub_mem (fun _ => a)
  change M.neg (M.nand (M.choice a) a) = M.choice a at equation
  exact ((S.meet _ _ _ _).mp (equation.symm ▸ h)).2

theorem choice_functional (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (a : A) {x y z : Point} (hy : S.rel (M.choice a) x y) (hz : S.rel (M.choice a) x z) :
    y = z := by
  classical
  have equation := hM choiceFunctional choiceFunctional_mem (fun _ => a)
  change M.neg (M.nand (M.product (M.converse (M.choice a)) (M.choice a))
    (M.neg (M.constant .I))) = M.neg (M.constant .U) at equation
  have hRel := Iff.of_eq (congrArg (fun r => S.rel r y z) equation)
  simp only [S.meet, S.product, S.converse, S.complement, S.identity, S.universal,
    not_true_eq_false, iff_false] at hRel
  exact Classical.byContradiction (fun hne => hRel ⟨⟨x, hy, hz⟩, hne⟩)

theorem choice_domain (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (a : A) (x : Point) :
    (∃ y, S.rel (M.choice a) x y) ↔ ∃ y, S.rel a x y := by
  have equation := hM choiceDomain choiceDomain_mem (fun _ => a)
  change M.product (M.choice a) (M.constant .U) = M.product a (M.constant .U) at equation
  have hRel := Iff.of_eq (congrArg (fun r => S.rel r x x) equation)
  simpa only [S.product, S.universal, and_true] using hRel

/-- For each algebra element, the image of the members of a set under that
element's selector is represented by a set in the membership structure. -/
theorem exact_image (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (a : A) (x : Point) :
    ∃ y, ∀ z, S.rel (M.constant .E) z y ↔
      ∃ w, S.rel (M.constant .E) w x ∧ S.rel (M.choice a) w z := by
  classical
  let e := M.constant .E
  let u := M.constant .U
  let image := M.product (M.converse e) (M.choice a)
  have equation := hM imageEquation image_mem (fun _ => a)
  change M.product (M.neg (M.nand (M.neg (M.product image (M.neg e)))
    (M.neg (M.product (M.neg image) e)))) u = u at equation
  have hRel := Iff.of_eq (congrArg (fun r => S.rel r x x) equation)
  simp only [S.meet, S.product, S.complement] at hRel
  obtain ⟨y, ⟨noExtra, noMissing⟩, _⟩ := hRel.mpr ((S.universal x x).mpr trivial)
  refine ⟨y, fun z => ?_⟩
  have hImage := S.product (M.converse e) (M.choice a) x z
  simp only [S.converse] at hImage
  rw [← hImage]
  constructor
  · intro hz
    exact Classical.byContradiction (fun hn => noMissing ⟨z, hn, hz⟩)
  · intro hz
    exact Classical.byContradiction (fun hn => noExtra ⟨z, hz, hn⟩)

theorem exact_image_of_functional (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (a : A) (hFun : ∀ x y z, S.rel a x y → S.rel a x z → y = z) (x : Point) :
    ∃ y, ∀ z, S.rel (M.constant .E) z y ↔
      ∃ w, S.rel (M.constant .E) w x ∧ S.rel a w z := by
  have selector_eq (w z : Point) : S.rel (M.choice a) w z ↔ S.rel a w z := by
    constructor
    · exact S.choice_sub hM a
    · intro h
      obtain ⟨picked, hp⟩ := (S.choice_domain hM a w).mpr ⟨z, h⟩
      have hEq := hFun w picked z (S.choice_sub hM a hp) h
      exact hEq ▸ hp
  simpa only [selector_eq] using S.exact_image hM a x

theorem subset_iff (S : SquareRepresentation M Point) (hM : M.Models preceding) (x y : Point) :
    S.rel (M.constant .T) x y ↔
      ∀ z, S.rel (M.constant .E) z x → S.rel (M.constant .E) z y := by
  classical
  have equation := hM defineSubset (by simp [preceding]) (fun _ => M.constant .U)
  change M.constant .T = M.neg (M.product (M.converse (M.constant .E))
    (M.neg (M.constant .E))) at equation
  rw [equation, S.complement, S.product]
  simp only [S.converse, S.complement]
  constructor
  · intro h z hz
    exact Classical.byContradiction fun hn => h ⟨z, hz, hn⟩
  · rintro h ⟨z, hz, hn⟩
    exact hn (h z hz)

theorem extensional (S : SquareRepresentation M Point) (hM : M.Models preceding) {x y : Point}
    (h : ∀ z, S.rel (M.constant .E) z x ↔ S.rel (M.constant .E) z y) : x = y := by
  have equation := hM extensionality (by simp [preceding, retained]) (fun _ => M.constant .U)
  change M.neg (M.nand (M.constant .T) (M.converse (M.constant .T))) = M.constant .I at equation
  have hRel : S.rel (M.neg (M.nand (M.constant .T) (M.converse (M.constant .T)))) x y := by
    rw [S.meet, S.converse, S.subset_iff hM, S.subset_iff hM]
    exact ⟨fun z => (h z).mp, fun z => (h z).mpr⟩
  rw [equation, S.identity] at hRel
  exact hRel

/-- The empty relation's selector has an empty image at every input point. -/
theorem exists_empty (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (x : Point) : ∃ y, ∀ z, ¬ S.rel (M.constant .E) z y := by
  obtain ⟨y, hy⟩ := S.exact_image hM (M.neg (M.constant .U)) x
  refine ⟨y, fun z hz => ?_⟩
  obtain ⟨w, _, hw⟩ := (hy z).mp hz
  exact (S.complement _ _ _).mp (S.choice_sub hM _ hw) ((S.universal _ _).mpr trivial)

end SquareRepresentation
end PalomarI3380
