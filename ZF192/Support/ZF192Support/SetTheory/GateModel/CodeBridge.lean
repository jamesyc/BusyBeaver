module
public import ZF192Support.SetTheory.GateModel.ZFModel
@[expose] public section
/-! # The membership-indiscernibility quotient -/
namespace ZF192Support.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

section Indisc
variable {W : Type*} (mem : W → W → Prop)

/-- Indiscernibility by membership. -/
def Indisc (x y : W) : Prop := ∀ z, (mem z x ↔ mem z y) ∧ (mem x z ↔ mem y z)

def indiscSetoid : Setoid W where
  r := Indisc mem
  iseqv := ⟨fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, fun h z => ⟨(h z).1.symm, (h z).2.symm⟩,
    fun h₁ h₂ z => ⟨(h₁ z).1.trans (h₂ z).1, (h₁ z).2.trans (h₂ z).2⟩⟩

/-- The indiscernibility quotient. -/
def NQ := Quotient (indiscSetoid mem)

instance : SetStructure (NQ mem) where
  mem Y X := Quotient.lift₂ (s₁ := indiscSetoid mem) (s₂ := indiscSetoid mem)
    (fun x y => mem x y) (fun _ y₁ x₂ _ hx hy => propext ((hx y₁).2.trans (hy x₂).1)) X Y

/-- The class of an object. -/
def cls (x : W) : NQ mem := Quotient.mk (indiscSetoid mem) x

lemma cls_mem {x y : W} : cls mem x ∈ cls mem y ↔ mem x y := Iff.rfl

lemma cls_eq {x y : W} : cls mem x = cls mem y ↔ Indisc mem x y :=
  Quotient.eq (r := indiscSetoid mem)

lemma cls_surj (X : NQ mem) : ∃ x, cls mem x = X := Quotient.exists_rep X

end Indisc

universe u

section Bridge
variable {W : Type u} [Nonempty W] {mem : W → W → Prop} {e : W} (he : ∀ y, ¬ mem y e)

include he

/-- The class of the empty object is empty. -/
lemma nq_isEmpty : SetTheory.IsEmpty (cls mem e) := by
  intro Y hY
  obtain ⟨y, rfl⟩ := cls_surj mem Y
  exact he y hY

omit he in
instance : Nonempty (NQ mem) := ⟨cls mem (Classical.arbitrary W)⟩

end Bridge

end ZF192Support.GateModel
