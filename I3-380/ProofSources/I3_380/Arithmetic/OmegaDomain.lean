module
public import I3_380.Arithmetic.OmegaOperations
public import I3_380.ClassModel
public import Foundation.FirstOrder.Arithmetic.Basic.Model
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}

/-- The natural numbers of an ordinary or expanded membership model. -/
structure OmegaDomain (L : ClassAxioms E G) (inhabited : Nonempty V) where
  omega : V
  specification : Internal.Omega E omega

namespace OmegaDomain

variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)

def Points := {x : V // E x D.omega}

noncomputable instance : Zero D.Points := ⟨⟨(K).empty,(K).omega_zero D.specification⟩⟩

noncomputable def successor (a : D.Points) : D.Points :=
  ⟨(K).succ a.val,(K).omega_succ D.specification a.property⟩

noncomputable instance : One D.Points := ⟨D.successor 0⟩

noncomputable instance : Add D.Points where
  add a b :=
    let h := (K).add_total D.specification a.property b.property
    ⟨Classical.choose h,((K).natObject_iff D.specification _).mp (Classical.choose_spec h).2.2.1⟩

noncomputable instance : Mul D.Points where
  mul a b :=
    let h := (K).mul_total D.specification a.property b.property
    ⟨Classical.choose h,((K).natObject_iff D.specification _).mp (Classical.choose_spec h).2.2.1⟩

instance : LT D.Points := ⟨fun a b => E a.val b.val⟩

instance : Nonempty D.Points := ⟨0⟩

noncomputable def numeral (n : Nat) : D.Points :=
  ⟨(K).numeral n, (K).numeral_in_omega D.specification n⟩

theorem zero_value : (0 : D.Points).val = (K).empty := rfl

theorem add_value (a b : D.Points) : Internal.Add E a.val b.val (a+b).val :=
  Classical.choose_spec ((K).add_total D.specification a.property b.property)

theorem mul_value (a b : D.Points) : Internal.Mul E a.val b.val (a*b).val :=
  Classical.choose_spec ((K).mul_total D.specification a.property b.property)

theorem add_result (a b : D.Points) (c : V) :
    Internal.Add E a.val b.val c ↔ c = (a+b).val :=
  ⟨fun h => (K).add_unique D.specification h (D.add_value a b),
    fun h => h.symm ▸ D.add_value a b⟩

theorem mul_result (a b : D.Points) (c : V) :
    Internal.Mul E a.val b.val c ↔ c = (a*b).val :=
  ⟨fun h => (K).mul_unique D.specification h (D.mul_value a b),
    fun h => h.symm ▸ D.mul_value a b⟩

theorem plus_zero (a : D.Points) : a + 0 = a :=
  Subtype.ext (((D.add_result a 0 a.val).mp ((K).add_zero D.specification a.property)).symm)

theorem plus_succ (a b : D.Points) : a + D.successor b = D.successor (a+b) :=
  Subtype.ext (((D.add_result a (D.successor b) (D.successor (a+b)).val).mp
    ((K).add_succ D.specification (D.add_value a b))).symm)

theorem plus_one (a : D.Points) : a + 1 = D.successor a := by
  change a + D.successor 0 = D.successor a
  rw [D.plus_succ,D.plus_zero]

theorem times_zero (a : D.Points) : a * 0 = 0 :=
  Subtype.ext (((D.mul_result a 0 ((0 : D.Points).val)).mp ((K).mul_zero D.specification a.property)).symm)

theorem times_succ (a b : D.Points) : a * D.successor b = a*b+a :=
  Subtype.ext (((D.mul_result a (D.successor b) (a*b+a).val).mp
    ((K).mul_succ D.specification (D.mul_value a b) (D.add_value (a*b) a))).symm)

theorem lt_successor (a b : D.Points) : a < D.successor b ↔ a < b ∨ a = b := by
  exact ((K).mem_succ b.val a.val).trans (or_congr Iff.rfl Subtype.ext_iff.symm)

theorem lt_succ_self (a : D.Points) : a < D.successor a :=
  (D.lt_successor _ _).mpr (Or.inr rfl)

theorem nat_predecessor (a : D.Points) : a = 0 ∨ ∃ b, D.successor b = a := by
  have zero := Definable.empty (N := (K)) (n := 2) (i := 0) (by decide)
  have before := Definable.mem (N := (K)) (n := 3) (i := 0) (j := 2) (by decide) (by decide)
  have next := Definable.successor (N := (K)) (n := 3) (i := 0) (j := 1) (by decide) (by decide)
  have all := (K).omega_induction D.specification [] (zero.or (Definable.ex (before.and next))) D.omega
    (Or.inl (K).empty_mem) (fun x hx _ => Or.inr ⟨x,hx,(K).mem_succ x⟩)
  rcases all a.val a.property with zero | ⟨x,hx,step⟩
  · exact Or.inl (Subtype.ext (((K).empty_unique a.val).mp zero))
  · exact Or.inr ⟨⟨x,hx⟩,Subtype.ext (((K).internal_succ x a.val).mp step).symm⟩

theorem lt_trichotomy (a b : D.Points) : a < b ∨ a = b ∨ b < a := by
  have ord := (K).omega_ordinal D.specification
  exact (ord.ordered.compare _ _ a.property b.property).imp_right (Or.imp_left Subtype.ext)

theorem lt_irrefl (a : D.Points) : ¬a < a :=
  ((K).omega_ordinal D.specification).ordered.irrefl _ a.property

theorem lt_trans {a b c : D.Points} (ab : a < b) (bc : b < c) : a < c :=
  ((K).omega_ordinal D.specification).ordered.trans _ _ _ a.property b.property c.property ab bc

theorem zero_le (a : D.Points) : (0 : D.Points) < a ∨ (0 : D.Points) = a := by
  rcases D.lt_trichotomy 0 a with lower | eq | empty
  · exact Or.inl lower
  · exact Or.inr eq
  · exact ((K).empty_mem _ empty).elim

theorem succ_mono {a b : D.Points} (ab : a < b) : D.successor a < D.successor b := by
  rcases D.lt_trichotomy (D.successor a) b with below | same | above
  · exact (D.lt_successor _ _).mpr (Or.inl below)
  · exact (D.lt_successor _ _).mpr (Or.inr same)
  · rcases (D.lt_successor b a).mp above with back | eq
    · exact (D.lt_irrefl a (D.lt_trans ab back)).elim
    · exact (D.lt_irrefl a (eq ▸ ab)).elim

end OmegaDomain
end PalomarI3380.Logic.Expanded
