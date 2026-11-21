module
public import I3_380.LocalRelations
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}
variable (hM : M.Models preceding) (closed : S.LocalClosure)
include hM closed

theorem twisted_product_value {r s : Relation Point} (hr : S.LocalValue r) (hs : S.LocalValue s) :
    S.LocalValue (relProduct r (relConverse s)) := by
  have zero := empty_local_value hM (top_value hM closed)
  exact (w_value hM hr hs zero).congr fun x y => by simp [constructorW, relProduct, relConverse]

theorem converse_value {r : Relation Point} (hr : S.LocalValue r) (supports : S.Supported r) :
    S.LocalValue (relConverse r) := by
  refine (twisted_product_value hM closed (identity_value hM closed) hr).congr fun x y => ?_
  constructor
  · rintro ⟨u, ⟨_, rfl⟩, hu⟩
    exact hu
  · intro hy
    have h := supports y x hy
    exact ⟨x, ⟨⟨h.2, h.2⟩, rfl⟩, hy⟩

theorem product_value {r s : Relation Point} (hr : S.LocalValue r) (hs : S.LocalValue s)
    (supports : S.Supported s) : S.LocalValue (relProduct r s) :=
  twisted_product_value hM closed hr (converse_value hM closed hs supports)

theorem conjoin_value {r s : Relation Point} (hr : S.LocalValue r) (hs : S.LocalValue s)
    (supportR : S.Supported r) (supportS : S.Supported s) :
    S.LocalValue (relMeet r s) := by
  classical
  let plus : Relation Point := fun x y => r x y ∨ S.localIdentity x y
  have ht := top_value hM closed
  have hi := identity_value hM closed
  have hn := complement_value hM ht hr
  have hPlus : S.LocalValue plus := by
    have hDrop : S.LocalValue (fun x y => S.relativeNot r x y ∧ ¬ S.localIdentity x y) := by
      refine (w_value hM hn hi hi).congr fun x y => ?_
      simp only [constructorW, and_self, relativeNot, localIdentity, localTop]
      constructor
      · rintro ⟨⟨z, ⟨⟨hx, hz⟩, no⟩, ⟨_, hy⟩, rfl⟩, ne⟩
        exact ⟨⟨⟨hx, hy⟩, no⟩, ne⟩
      · rintro ⟨⟨⟨hx, hy⟩, no⟩, ne⟩
        exact ⟨⟨y, ⟨⟨hx, hy⟩, no⟩, ⟨hy, hy⟩, rfl⟩, ne⟩
    refine (complement_value hM ht hDrop).congr fun x y => ?_
    constructor
    · rintro ⟨top, no⟩
      by_cases yes : r x y
      · exact Or.inl yes
      · exact Or.inr (Classical.byContradiction fun notI => no ⟨⟨top, yes⟩, notI⟩)
    · intro edge
      exact ⟨edge.elim (supportR x y) And.left, fun no =>
        edge.elim no.1.2 no.2⟩
  have hPlusSupport : S.Supported plus := fun x y h => h.elim (supportR x y) And.left
  have negBoth : S.LocalValue (S.relativeNot (relMeet plus s)) := by
    refine (w_value hM ht hPlus hs).congr fun x y => ?_
    have full : (∃ z, S.localTop x z ∧ plus y z) ↔ S.localTop x y := by
      constructor
      · rintro ⟨z, hxz, hyz⟩
        exact ⟨hxz.1, (hPlusSupport y z hyz).1⟩
      · rintro ⟨hx, hy⟩
        exact ⟨y, ⟨hx, hy⟩, Or.inr ⟨⟨hy, hy⟩, rfl⟩⟩
    simp only [constructorW, relativeNot, relMeet, full]
  have both : S.LocalValue (relMeet plus s) := by
    refine (complement_value hM ht negBoth).congr fun x y => ?_
    change (S.localTop x y ∧ ¬ (S.localTop x y ∧ ¬ relMeet plus s x y)) ↔ _
    exact ⟨fun ⟨h, n⟩ => Classical.byContradiction fun absent => n ⟨h, absent⟩,
      fun h => ⟨supportS x y h.2, fun no => no.2 h⟩⟩
  refine (w_value hM both hi hn).congr fun x y => ?_
  constructor
  · rintro ⟨⟨z, ⟨union, member⟩, ⟨_, rfl⟩⟩, ne⟩
    refine ⟨union.elim id (fun idEdge => ?_), member⟩
    exact Classical.byContradiction fun no => ne ⟨idEdge, idEdge.1, no⟩
  · rintro ⟨hx, hy⟩
    have good := supportR x y hx
    exact ⟨⟨y, ⟨Or.inl hx, hy⟩, ⟨⟨good.2, good.2⟩, rfl⟩⟩, fun no => no.2.2 hx⟩

/-- Relations in the active domain that are obtained from the single
seed by the constructor equation, restricted to the supported outputs. -/
structure LocalRelation (S : SquareRepresentation M Point) where
  rel : Relation Point
  supported : S.Supported rel
  generated : S.LocalValue rel

namespace LocalRelation

def zero (hM : M.Models preceding) (closed : S.LocalClosure) : LocalRelation S :=
  ⟨fun _ _ => False, fun _ _ h => h.elim, empty_local_value hM (top_value hM closed)⟩

def top (hM : M.Models preceding) (closed : S.LocalClosure) : LocalRelation S :=
  ⟨S.localTop, fun _ _ h => h, top_value hM closed⟩

def one (hM : M.Models preceding) (closed : S.LocalClosure) : LocalRelation S :=
  ⟨S.localIdentity, fun _ _ h => h.1, identity_value hM closed⟩

def member (hM : M.Models preceding) (closed : S.LocalClosure) : LocalRelation S :=
  ⟨S.localSeed, fun _ _ h => ⟨closed.transitive h, h.2⟩, S.seed_value hM⟩

def neg (hM : M.Models preceding) (closed : S.LocalClosure) (r : LocalRelation S) : LocalRelation S :=
  ⟨S.relativeNot r.rel, fun _ _ h => h.1, complement_value hM (top_value hM closed) r.generated⟩

def conv (hM : M.Models preceding) (closed : S.LocalClosure) (r : LocalRelation S) : LocalRelation S :=
  ⟨relConverse r.rel, fun x y h => (r.supported y x h).symm, converse_value hM closed r.generated r.supported⟩

def prod (hM : M.Models preceding) (closed : S.LocalClosure) (r s : LocalRelation S) : LocalRelation S :=
  ⟨relProduct r.rel s.rel, fun _ _ ⟨_, h, k⟩ => ⟨(r.supported _ _ h).1, (s.supported _ _ k).2⟩,
    product_value hM closed r.generated s.generated s.supported⟩

def inf (hM : M.Models preceding) (closed : S.LocalClosure) (r s : LocalRelation S) : LocalRelation S :=
  ⟨relMeet r.rel s.rel, fun x y h => r.supported x y h.1,
    conjoin_value hM closed r.generated s.generated r.supported s.supported⟩

def algebra (hM : M.Models preceding) (closed : S.LocalClosure) : Algebra (LocalRelation S) where
  constant
    | .E => member hM closed
    | .I => one hM closed
    | .U => top hM closed
    | _ => zero hM closed
  neg := neg hM closed
  converse := conv hM closed
  nand r s := neg hM closed (inf hM closed r s)
  product := prod hM closed
  choice := id
  localRel := id
  node r _ _ := r

def square (hM : M.Models preceding) (closed : S.LocalClosure) :
    SquareRepresentation (algebra hM closed) {x : Point // S.activePoint x} where
  rel r x y := r.rel x.val y.val
  complement _ x y := ⟨And.right, fun h => ⟨⟨x.property, y.property⟩, h⟩⟩
  converse _ _ _ := Iff.rfl
  nand _ _ x y := ⟨And.right, fun h => ⟨⟨x.property, y.property⟩, h⟩⟩
  product r _ _ _ :=
    ⟨fun ⟨z, h, k⟩ => ⟨⟨z, (r.supported _ z h).2⟩, h, k⟩, fun ⟨z, h, k⟩ => ⟨z.val, h, k⟩⟩
  universal x y := ⟨fun _ => trivial, fun _ => ⟨x.property, y.property⟩⟩
  identity x y :=
    ⟨fun h => Subtype.ext h.2, fun h => ⟨⟨x.property, y.property⟩, congrArg Subtype.val h⟩⟩

theorem reflects (r : LocalRelation S) {x y u v : Point}
    (jx : S.rel (M.constant .J) x u) (jy : S.rel (M.constant .J) y v) :
    r.rel x y ↔ r.rel u v := by
  refine ⟨r.generated.preserved hM jx jy, fun h => ?_⟩
  apply Classical.byContradiction
  intro no
  have top : S.localTop x y := ⟨(j_active hM closed jx).1, (j_active hM closed jy).1⟩
  exact ((neg hM closed r).generated.preserved hM jx jy ⟨top, no⟩).2 h

end LocalRelation
end PalomarI3380.SquareRepresentation
