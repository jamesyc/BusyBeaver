module
public import I3_334Support.SetTheory.Square.SquareAxioms
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

abbrev Relation (Point : Type) := Point → Point → Prop

def activePoint (S : SquareRepresentation M Point) (x : Point) : Prop :=
  S.rel (M.constant .D) x x

def localTop (S : SquareRepresentation M Point) : Relation Point :=
  fun x y => S.activePoint x ∧ S.activePoint y

def localIdentity (S : SquareRepresentation M Point) : Relation Point :=
  fun x y => S.localTop x y ∧ x = y

def localSeed (S : SquareRepresentation M Point) : Relation Point :=
  fun x y => S.rel (M.constant .E) x y ∧ S.activePoint y

def relativeNot (S : SquareRepresentation M Point) (r : Relation Point) : Relation Point :=
  fun x y => S.localTop x y ∧ ¬r x y

def relMeet (r s : Relation Point) : Relation Point := fun x y => r x y ∧ s x y
def relProduct (r s : Relation Point) : Relation Point := fun x y => ∃ z, r x z ∧ s z y
def relConverse (r : Relation Point) : Relation Point := fun x y => r y x

def constructorW (r s t : Relation Point) : Relation Point :=
  fun x y => (∃ z, r x z ∧ s y z) ∧ ¬(s x y ∧ t x y)

def LocalValue (S : SquareRepresentation M Point) (r : Relation Point) : Prop :=
  ∃ a : A, ∀ x y, S.rel (M.localRel a) x y ↔ r x y

theorem LocalValue.congr {r s : Relation Point} (h : S.LocalValue r)
    (equal : ∀ x y, r x y ↔ s x y) : S.LocalValue s := by
  obtain ⟨a, spec⟩ := h
  exact ⟨a, fun x y => (spec x y).trans (equal x y)⟩

theorem seed_value (S : SquareRepresentation M Point) (hM : M.Models preceding) :
    S.LocalValue S.localSeed := by
  let e := M.constant .E
  let d := M.constant .D
  have law := hM (Term.localRel (.const .I), Term.product (.const .E) (.const .D))
    (by simp [preceding, retained]) (fun _ => M.constant .U)
  change M.localRel (M.constant .I) = M.product e d at law
  refine ⟨M.constant .I, fun x y => ?_⟩
  rw [law, S.product]
  constructor
  · rintro ⟨z, hz, dz⟩
    obtain rfl := (S.domain_eq hM z y |>.mp dz).1
    exact ⟨hz, dz⟩
  · rintro ⟨h, hy⟩
    exact ⟨y, h, hy⟩

theorem w_value (hM : M.Models preceding) {a b c : Relation Point}
    (ha : S.LocalValue a) (hb : S.LocalValue b) (hc : S.LocalValue c) :
    S.LocalValue (constructorW a b c) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain ⟨w, hw⟩ := hc
  have law := hM
    (Term.localRel (Term.node Manifest.a Manifest.b Manifest.c),
      Manifest.meet (Term.product (Term.localRel Manifest.a) (Term.converse (Term.localRel Manifest.b)))
        (Term.nand (Term.localRel Manifest.b) (Term.localRel Manifest.c)))
    (by simp [preceding, retained])
    (fun i => if i.val = 0 then u else if i.val = 1 then v else w)
  change M.localRel (M.node u v w) =
    M.inf (M.product (M.localRel u) (M.converse (M.localRel v))) (M.nand (M.localRel v) (M.localRel w)) at law
  refine ⟨M.node u v w, fun x y => ?_⟩
  simp only [law, Algebra.inf, S.meet, S.product, S.converse, S.nand, hu, hv, hw, constructorW]

theorem LocalValue.preserved {r : Relation Point} (h : S.LocalValue r)
    (hM : M.Models preceding) {x y u v : Point}
    (jx : S.rel (M.constant .J) x u) (jy : S.rel (M.constant .J) y v) (edge : r x y) :
    r u v := by
  let j : Term (Fin 3) := .const .J
  obtain ⟨a, described⟩ := h
  have law := hM
    (Manifest.meet (Term.product (Term.product (.converse j) (.localRel Manifest.a)) j)
      (.neg (.localRel Manifest.a)), .neg (.const .U))
    (by simp [preceding, retained, j]) (fun _ => a)
  change M.inf (M.product (M.product (M.converse (M.constant .J)) (M.localRel a)) (M.constant .J))
    (M.neg (M.localRel a)) = M.neg (M.constant .U) at law
  apply Classical.byContradiction
  intro missing
  have bad : S.rel (M.inf
    (M.product (M.product (M.converse (M.constant .J)) (M.localRel a)) (M.constant .J))
    (M.neg (M.localRel a))) u v := by
    simp only [Algebra.inf, S.meet, S.product, S.converse, S.complement, described]
    exact ⟨⟨y, ⟨x, jx, edge⟩, jy⟩, missing⟩
  rw [law, S.complement, S.universal] at bad
  exact bad trivial

def Supported (S : SquareRepresentation M Point) (r : Relation Point) : Prop :=
  ∀ x y, r x y → S.localTop x y

variable (hM : M.Models preceding)
include hM

theorem complement_value {r : Relation Point} (top : S.LocalValue S.localTop) (hr : S.LocalValue r) :
    S.LocalValue (S.relativeNot r) := by
  refine (w_value hM top top hr).congr fun x y => ?_
  simp only [constructorW, localTop, relativeNot]
  constructor
  · rintro ⟨⟨z, ⟨hx, _⟩, hy, _⟩, no⟩
    exact ⟨⟨hx, hy⟩, fun e => no ⟨⟨hx, hy⟩, e⟩⟩
  · rintro ⟨⟨hx, hy⟩, no⟩
    exact ⟨⟨x, ⟨hx, hx⟩, hy, hx⟩, fun h => no h.2⟩

structure LocalClosure (S : SquareRepresentation M Point) : Prop where
  transitive : ∀ {x y}, S.localSeed x y → S.activePoint x
  pairs : ∀ {x y}, S.activePoint x → S.activePoint y →
    ∃ p, S.activePoint p ∧ Logic.Internal.Pair (S.rel (M.constant .E)) x y p

theorem top_value (closed : LocalClosure S) : S.LocalValue S.localTop := by
  have joint (x y : Point) : (∃ z, S.localSeed x z ∧ S.localSeed y z) ↔ S.localTop x y := by
    constructor
    · rintro ⟨z, hx, hy⟩
      exact ⟨closed.transitive hx, closed.transitive hy⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨p, act, pair⟩ := closed.pairs hx hy
      exact ⟨p, ⟨(pair x).mpr (Or.inl rfl), act⟩, (pair y).mpr (Or.inr rfl), act⟩
  have seed := S.seed_value hM
  have opposite : S.LocalValue (S.relativeNot S.localSeed) := by
    refine (w_value hM seed seed seed).congr fun x y => ?_
    simp only [constructorW, joint, and_self, relativeNot]
  refine (w_value hM seed seed opposite).congr fun x y => ?_
  simp only [constructorW, joint, relativeNot]
  exact ⟨And.left, fun h => ⟨h, fun no => no.2.2 no.1⟩⟩

theorem empty_local_value (top : S.LocalValue S.localTop) :
    S.LocalValue (fun _ _ => False) := by
  exact (complement_value hM top top).congr fun x y => by
    simp only [relativeNot, and_not_self]

theorem identity_value (closed : LocalClosure S) : S.LocalValue S.localIdentity := by
  let seed := S.localSeed
  have ht := top_value hM closed
  have he := S.seed_value hM
  have hn := complement_value hM ht he
  have hzero := empty_local_value hM ht
  let diversity : Relation Point := fun x y => S.localTop x y ∧ x ≠ y
  have hd : S.LocalValue diversity := by
    refine (w_value hM he hn hzero).congr fun x y => ?_
    simp only [constructorW, and_false, not_false_eq_true, and_true, relativeNot, localTop, diversity]
    constructor
    · rintro ⟨z, hx, ⟨hy, _⟩, missing⟩
      exact ⟨⟨closed.transitive hx, hy⟩, fun eq => missing (eq ▸ hx)⟩
    · rintro ⟨⟨hx, hy⟩, different⟩
      obtain ⟨p, hp, elems⟩ := closed.pairs hx hx
      have miss : ¬S.rel (M.constant .E) y p := fun h =>
        different (((elems y).mp h).elim Eq.symm Eq.symm)
      exact ⟨p, ⟨(elems x).mpr (Or.inl rfl), hp⟩, ⟨hy, hp⟩, fun h => miss h.1⟩
  refine (complement_value hM ht hd).congr fun x y => ?_
  change S.localTop x y ∧ ¬(S.localTop x y ∧ x ≠ y) ↔ S.localTop x y ∧ x = y
  constructor
  · exact fun ⟨h, hd⟩ => ⟨h, Classical.byContradiction fun ne => hd ⟨h, ne⟩⟩
  · exact fun ⟨h, same⟩ => ⟨h, fun hd => hd.2 same⟩

theorem j_active {x y : Point} (closed : LocalClosure S) (edge : S.rel (M.constant .J) x y) :
    S.activePoint x ∧ S.activePoint y := by
  have origin : S.activePoint x := (S.domain_eq hM x x).mpr ⟨rfl, y, edge⟩
  exact ⟨origin, ((top_value hM closed).preserved hM edge edge ⟨origin, origin⟩).1⟩

theorem j_single_valued (closed : LocalClosure S) {x y z : Point}
    (first : S.rel (M.constant .J) x y) (second : S.rel (M.constant .J) x z) : y = z := by
  have source := (j_active hM closed first).1
  exact ((identity_value hM closed).preserved hM first second ⟨⟨source, source⟩, rfl⟩).2

theorem j_injective (closed : LocalClosure S) {x y z : Point}
    (first : S.rel (M.constant .J) x z) (second : S.rel (M.constant .J) y z) : x = y := by
  apply Classical.byContradiction
  intro different
  have sourceX := j_active hM closed first
  have sourceY := j_active hM closed second
  have hNot := complement_value hM (top_value hM closed) (identity_value hM closed)
  exact (hNot.preserved hM first second ⟨⟨sourceX.1, sourceY.1⟩, fun he => different he.2⟩).2
    ⟨⟨sourceX.2, sourceX.2⟩, rfl⟩

end PalomarI3380.SquareRepresentation
