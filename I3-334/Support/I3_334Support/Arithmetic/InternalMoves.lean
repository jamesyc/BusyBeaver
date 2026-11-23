module
public import I3_334Support.Arithmetic.InternalConfiguration
public import I3_334Support.Arithmetic.Numerals
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

theorem bitValue_cast (b : Bool) : D.bitValue b = (b.toNat : W) := by
  cases b <;> simp [bitValue]

theorem bit_remainder (b : Bool) (a x : W) (h : x = D.bitValue b + 2*a) :
    remIn x 2 = D.bitValue b ∧ divIn x 2 = a := by
  have small : D.bitValue b < 2 := by cases b <;> simp [bitValue]
  rw [h,add_comm]
  exact ⟨by
    change (2*a+D.bitValue b) % 2 = D.bitValue b
    rw [mod_mul_add' _ _ (by simp)]
    exact mod_eq_self_of_lt small,
    div_mul_add' _ _ small⟩

theorem quotient_remainder (x : W) :
    x = remIn x 2 + 2 * divIn x 2 := by
  have h := Arithmetic.div_add_mod x 2
  change 2 * divIn x 2 + remIn x 2 = x at h
  exact (h.symm.trans (add_comm _ _))

theorem bit_read (x : W) : ∃ b : Bool, remIn x 2 = D.bitValue b := by
  rcases mod_two x with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

noncomputable def moveResult (s : Configuration D) (write right : Bool) (next : Nat) : Configuration D :=
  if right then
    ⟨(next : W), D.bitValue write+2*s.left, divIn s.right 2⟩
  else
    ⟨(next : W), divIn s.left 2,
      remIn s.left 2 + 2*(D.bitValue write+2*divIn s.right 2)⟩

theorem move_eval (s t : Configuration D) (read write right : Bool) (next : Nat) :
    Internal.Move E read write right next s.raw t.raw ↔
      remIn s.right 2 = D.bitValue read ∧ t = D.moveResult s write right next := by
  constructor
  · rintro ⟨tail,edge,number,writeBack⟩
    let tail' : W := ⟨tail,(D.bitCons_natural edge).1⟩
    have input : Internal.BitCons E read tail'.val s.right.val := edge
    obtain ⟨readBit,tailEq⟩ := D.bit_remainder read tail' s.right ((D.bitCons_eval _ _ _).mp input)
    have state : t.state = (next : W) :=
      Subtype.ext ((D.numeral_value (n := next)).mp number)
    refine ⟨readBit,?_⟩
    cases right
    · obtain ⟨left,head,middle,leftEdge,leftValue,writeMid,writeRight⟩ := writeBack
      let left' : W := ⟨left,(D.bitCons_natural leftEdge).1⟩
      let mid : W := ⟨middle,(D.bitCons_natural writeMid).2⟩
      have leftSplit : Internal.BitCons E head left'.val s.left.val := leftEdge
      obtain ⟨headEq,leftEq⟩ := D.bit_remainder head left' s.left ((D.bitCons_eval _ _ _).mp leftSplit)
      have leftResult : t.left = divIn s.left 2 :=
        (Subtype.ext leftValue).trans leftEq.symm
      have middleResult : mid = D.bitValue write+2*tail' := (D.bitCons_eval _ tail' mid).mp writeMid
      have rightResult : t.right = D.bitValue head+2*mid := (D.bitCons_eval _ mid _).mp writeRight
      have rightEq : t.right = remIn s.left 2+2*(D.bitValue write+2*divIn s.right 2) := by
        rw [rightResult,middleResult,headEq,tailEq]
      cases t
      simp only [moveResult,Bool.false_eq_true,↓reduceIte] at *
      congr 1
    · obtain ⟨left,tailValue⟩ := writeBack
      have leftEq := (D.bitCons_eval write s.left t.left).mp left
      have rightEq : t.right = divIn s.right 2 :=
        (Subtype.ext tailValue).trans tailEq.symm
      cases t
      simp only [moveResult,Bool.true_eq,↓reduceIte] at *
      congr 1
  · rintro ⟨bit,rfl⟩
    let tail := divIn s.right 2
    have source : Internal.BitCons E read tail.val s.right.val :=
      (D.bitCons_eval _ _ _).mpr ((D.quotient_remainder s.right).trans (by rw [bit]))
    have state : Internal.Numeral E next ((D.moveResult s write right next).state.val) := by
      apply D.numeral_value.mpr
      cases right <;> rfl
    refine ⟨tail.val,source,state,?_⟩
    cases right
    · obtain ⟨head,headEq⟩ := D.bit_read s.left
      let left := divIn s.left 2
      let middle := D.bitValue write+2*tail
      have leftEdge := (D.bitCons_eval head left s.left).mpr
        ((D.quotient_remainder s.left).trans (by rw [headEq]))
      refine ⟨left.val,head,middle.val,leftEdge,rfl,(D.bitCons_eval write tail middle).mpr rfl,
        (D.bitCons_eval head middle (D.moveResult s write false next).right).mpr ?_⟩
      change remIn s.left 2 + 2*middle = _
      rw [headEq]
    · exact ⟨(D.bitCons_eval write s.left (D.moveResult s write true next).left).mpr rfl,rfl⟩

end PalomarI3380.Logic.Expanded.OmegaDomain
