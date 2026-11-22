module
public import ZF192Support.SetTheory.GateModel.Bisim
@[expose] public section
/-! # The marked quotient

Marked objects modulo marked bisimilarity, with membership given by marked
members up to bisimilarity. This is the interpreted universe. -/
namespace ZF192Support.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [GateHull V]
variable {e : V} (he : SetTheory.IsEmpty e)

/-- Objects containing the marker `e`. -/
def Marked (e : V) := {x : V // e ∈ x}

/-- A bisimulation step relates marked members. -/
lemma Bisim.eqv {B x y : V} (hB : Bisim e B) (h : x = y ∨ PairIn e B x y) : Eqv e x y :=
  h.elim Or.inl fun h => Or.inr ⟨B, hB, h⟩

/-- Membership up to bisimilarity: some marked member of `y` is bisimilar to `x`. -/
def QMem (e x y : V) : Prop := ∃ z ∈ y, e ∈ z ∧ Eqv e x z

include he

lemma QMem.congr_left {x x' y : V} (hx : Eqv e x x') (h : QMem e x y) : QMem e x' y := by
  obtain ⟨z, hz, hez, hxz⟩ := h
  exact ⟨z, hz, hez, (hx.symm he).trans he hxz⟩

lemma QMem.congr_right {x y y' : V} (hy : Eqv e y y') (h : QMem e x y) : QMem e x y' := by
  obtain ⟨z, hz, hez, hxz⟩ := h
  rcases hy with rfl | ⟨B, hB, hyy'⟩
  · exact ⟨z, hz, hez, hxz⟩
  obtain ⟨z', hz', hez', hzz'⟩ := (hB _ _ hyy').1 z hz hez
  exact ⟨z', hz', hez', hxz.trans he (hB.eqv hzz')⟩

/-- Marked bisimilarity as a setoid on marked objects. -/
def markedSetoid : Setoid (Marked e) where
  r x y := Eqv e x.1 y.1
  iseqv := ⟨fun _ => Or.inl rfl, fun h => h.symm he, fun h₁ h₂ => h₁.trans he h₂⟩

lemma markedSetoid_r {x y : Marked e} : (markedSetoid he).r x y ↔ Eqv e x.1 y.1 := Iff.rfl

/-- The interpreted universe. -/
def Q := Quotient (markedSetoid he)

instance : SetStructure (Q he) where
  mem Y X := Quotient.lift₂ (s₁ := markedSetoid he) (s₂ := markedSetoid he)
    (fun x y => QMem e x.1 y.1)
    (fun _ _ _ _ hx hy => propext
      ⟨fun h => ((h.congr_left he hx).congr_right he hy),
       fun h => ((h.congr_left he (hx.symm he)).congr_right he (hy.symm he))⟩) X Y

/-- The class of a marked object. -/
def Q.mk (x : V) (hx : e ∈ x) : Q he := Quotient.mk (markedSetoid he) ⟨x, hx⟩

lemma Q.mk_mem_mk {x y : V} (hx : e ∈ x) (hy : e ∈ y) :
    Q.mk he x hx ∈ Q.mk he y hy ↔ QMem e x y := Iff.rfl

lemma Q.mk_eq_mk {x y : V} (hx : e ∈ x) (hy : e ∈ y) :
    Q.mk he x hx = Q.mk he y hy ↔ Eqv e x y :=
  Quotient.eq (r := markedSetoid he)

lemma Q.ind {P : Q he → Prop} (h : ∀ x hx, P (Q.mk he x hx)) (X : Q he) : P X :=
  Quotient.ind (fun x => h x.1 x.2) X

/-- Members of a class are classes of marked members. -/
lemma Q.mem_mk_iff {X : Q he} {y : V} (hy : e ∈ y) :
    X ∈ Q.mk he y hy ↔ ∃ z, ∃ hz : e ∈ z, z ∈ y ∧ X = Q.mk he z hz := by
  induction X using Q.ind he with
  | h x hx =>
    rw [Q.mk_mem_mk]
    refine ⟨fun ⟨z, hz, hez, hxz⟩ => ⟨z, hez, hz, (Q.mk_eq_mk he hx hez).mpr hxz⟩,
      fun ⟨z, hez, hz, h⟩ => ⟨z, hz, hez, (Q.mk_eq_mk he hx hez).mp h⟩⟩

end ZF192Support.GateModel
