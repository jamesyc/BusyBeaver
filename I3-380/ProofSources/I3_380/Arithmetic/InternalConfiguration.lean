module
public import I3_380.Arithmetic.OmegaPeano
public import I3_380.Arithmetic.Clock
public import I3_380.FiniteGraphs
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open SquareRepresentation ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

theorem numeral_cast (n : Nat) : D.numeral n = (n : W) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ,D.plus_one]
    change D.successor (D.numeral n) = D.successor (n : W)
    rw [ih]

theorem nat_object (n : W) : Internal.NatObject E n.val :=
  ⟨D.omega,D.specification,n.property⟩

theorem numeral_value {n : Nat} {x : V} :
    Internal.Numeral E n x ↔ x = ((n : W).val) := by
  rw [← D.numeral_cast]
  exact (K).numeral_def n x

theorem lt_numeral_iff (x : W) (n : Nat) :
    x < (n : W) ↔ ∃ i < n, x = (i : W) := by
  rw [← D.numeral_cast]
  refine ((K).mem_numeral n x.val).trans ?_
  constructor
  · rintro ⟨i,inside,e⟩
    exact ⟨i,inside,(Subtype.ext e).trans (D.numeral_cast i)⟩
  · rintro ⟨i,inside,e⟩
    exact ⟨i,inside,congrArg Subtype.val (e.trans (D.numeral_cast i).symm)⟩

noncomputable def bitValue (b : Bool) : W := if b then 1 else 0

theorem bitCons_natural {b : Bool} {x y : V} (h : Internal.BitCons E b x y) :
    E x D.omega ∧ E y D.omega := by
  obtain ⟨_,_,_,_,_,mul,add⟩ := h
  exact ⟨((K).natObject_iff D.specification _).mp mul.2.1,
    ((K).natObject_iff D.specification _).mp add.2.2.1⟩

theorem bitCons_eval (b : Bool) (x y : W) :
    Internal.BitCons E b x.val y.val ↔ y = D.bitValue b + 2*x := by
  have bit : ((if b then 1 else 0 : Nat) : W) = D.bitValue b := by cases b <;> simp [bitValue]
  constructor
  · rintro ⟨digit,two,twice,hb,hTwo,prod,sum⟩
    rw [D.numeral_value,bit] at hb
    rw [D.numeral_value] at hTwo
    subst digit two
    have twiceEq := (D.mul_result (2 : W) x _).mp prod
    subst twice
    exact Subtype.ext ((D.add_result _ _ _).mp sum)
  · intro eq
    refine ⟨(D.bitValue b).val,(2 : W).val,((2 : W)*x).val,?_ ,?_ ,D.mul_value 2 x,?_⟩
    · rw [D.numeral_value,bit]
    · exact D.numeral_value.mpr rfl
    · exact eq.symm ▸ D.add_value _ _

structure Configuration (D : OmegaDomain L inhabited) where
  state : D.Points
  left : D.Points
  right : D.Points

namespace Configuration

variable {D}

def raw (c : Configuration D) : Internal.Configuration V :=
  ⟨c.state.val,c.left.val,c.right.val⟩

noncomputable def setCode (c : Configuration D) : V :=
  (K).orderedPair c.state.val ((K).orderedPair c.left.val c.right.val)

theorem encodes_set (c : Configuration D) (code : V) :
    Internal.ConfigurationCode E c.raw code ↔ code = c.setCode := by
  constructor
  · rintro ⟨_,_,_,pair,lr,qr⟩
    simpa only [setCode,raw,((K).orderedPair_iff _ _ _).mp lr] using ((K).orderedPair_iff _ _ _).mp qr
  · rintro rfl
    exact ⟨D.nat_object c.state,D.nat_object c.left,D.nat_object c.right,_,
      (K).orderedPair_intro _ _,(K).orderedPair_intro _ _⟩

noncomputable def code (c : Configuration D) : D.Points :=
  ArithmeticMachine.encode c.state c.left c.right

noncomputable def decode (c : D.Points) : Configuration D :=
  ⟨π₁ c,π₁ (π₂ c),π₂ (π₂ c)⟩

theorem decode_encode (c : Configuration D) : decode c.code = c := by
  cases c
  simp [decode,code,ArithmeticMachine.encode]

theorem encode_decode (c : D.Points) : (decode c).code = c :=
  ArithmeticMachine.encode_projections c

end Configuration

theorem typed_configuration {c : Internal.Configuration V} {p : V}
    (h : Internal.ConfigurationCode E c p) : ∃ typed : Configuration D, typed.raw = c := by
  obtain ⟨q,l,r⟩ := c
  obtain ⟨hq,hl,hr,_⟩ := h
  exact ⟨⟨⟨q,((K).natObject_iff D.specification _).mp hq⟩,
      ⟨l,((K).natObject_iff D.specification _).mp hl⟩,
      ⟨r,((K).natObject_iff D.specification _).mp hr⟩⟩,rfl⟩

theorem typed_code_unique {a b : Configuration D} (same : a.setCode = b.setCode) : a = b := by
  obtain ⟨stateEq,restEq⟩ := (K).orderedPair_inj same
  obtain ⟨leftEq,rightEq⟩ := (K).orderedPair_inj restEq
  cases a
  cases b
  congr 1 <;> exact Subtype.ext ‹_›

end PalomarI3380.Logic.Expanded.OmegaDomain
