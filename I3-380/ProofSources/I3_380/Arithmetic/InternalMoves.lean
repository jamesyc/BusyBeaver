module
public import I3_380.Arithmetic.InternalConfiguration
public import I3_380.Arithmetic.Numerals
public import I3_380.LiteralRows
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

private theorem bitFlag (n : Nat) : (Nat.mod n 2 == 1).toNat = Nat.mod n 2 := by
  rcases (show Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 from Nat.mod_two_eq_zero_or_one n) with h | h <;> simp [h]

theorem tick_move (s : Configuration D) (q : Fin 380) (read : Bool)
    (state : s.state = (q.val : W)) (input : remIn s.right 2 = D.bitValue read) :
    Configuration.decode (D := D) (tick 380 packedLiteral s.code) =
      D.moveResult s (sourceWrites q read) (sourceMovesRight q read) (sourceTarget q read) := by
  classical
  let row := sourceRow q read
  have guard : s.state < (380 : W) := (D.lt_numeral_iff s.state 380).mpr ⟨q.val,q.isLt,state⟩
  have lookup : digit packedLiteral s.state s.right = (row : W) := by
    change digit machine.packedRows s.state s.right = (row : W)
    rw [state,digit_at_row machine,input]
    cases read
    · simpa [bitValue,row] using congrArg (fun n : Nat => (n : W)) (sourceRow_lookup q false)
    · simpa [bitValue,row] using congrArg (fun n : Nat => (n : W)) (sourceRow_lookup q true)
  have wb : D.bitValue (Nat.mod (Nat.div row 2) 2 == 1) = Nat.mod (Nat.div row 2) 2 := by
    rw [D.bitValue_cast,bitFlag]
  have parity : remIn (row : W) 2 = 1 ↔ Nat.mod row 2 = 1 := by
    rw [← Nat.cast_two,remIn_cast]
    exact Nat.cast_eq_one
  have twice : (2 : W) * 2 = 4 := by
    exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
  have next : divIn (row : W) 4 = Nat.div row 4 := by
    simpa only [Nat.cast_ofNat] using divIn_cast (M := W) row 4
  have write : remIn (divIn (row : W) 2) 2 = D.bitValue (Nat.mod (Nat.div row 2) 2 == 1) := by
    rw [wb]
    have first := divIn_cast (M := W) row 2
    have second := remIn_cast (M := W) (Nat.div row 2) 2
    simpa only [Nat.cast_ofNat] using (congrArg (fun x => remIn x ((2 : Nat) : W)) first).trans second
  have unfoldTick :
      tick 380 packedLiteral s.code =
        if remIn (row : W) 2 = 1 then
          ArithmeticMachine.encode (divIn (row : W) 4) (2*s.left+remIn (divIn (row : W) 2) 2) (divIn s.right 2)
        else
          ArithmeticMachine.encode (divIn (row : W) 4) (divIn s.left 2)
            (4*divIn s.right 2+2*remIn (divIn (row : W) 2) 2+remIn s.left 2) := by
    simp only [tick,Configuration.code,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,
      Nat.cast_ofNat,guard,↓reduceIte,lookup]
  rw [unfoldTick]
  change _ = D.moveResult s _ (Nat.mod row 2 == 1) _
  simp only [parity,next,write,moveResult,sourceWrites_eq,sourceTarget_eq,← show row = sourceRow q read from rfl,beq_iff_eq]
  split
  · simp only [Configuration.decode,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,add_comm]
  · simp only [Configuration.decode,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
    rw [mul_add,← mul_assoc,twice]
    rw [add_comm (2 * D.bitValue (Nat.mod (Nat.div row 2) 2 == 1)) (4 * divIn s.right 2)]
    rw [add_comm (4 * divIn s.right 2 + 2 * D.bitValue (Nat.mod (Nat.div row 2) 2 == 1)) (remIn s.left 2)]

theorem literalStep_eval (s t : Configuration D) :
    Internal.LiteralStep E s.raw t.raw ↔
      s.state < (380 : W) ∧ Configuration.decode (D := D) (tick 380 packedLiteral s.code) = t := by
  have rowShape (q : Fin 380) (read : Bool) :
      literal[2*q.val+(if read then 1 else 0)]?.getD 0 = sourceRow q read := by cases read <;> rfl
  constructor
  · rintro ⟨q,atQ,read,edge⟩
    have state : s.state = (q.val : W) := Subtype.ext (D.numeral_value.mp atQ)
    rw [rowShape] at edge
    obtain ⟨input,moved⟩ := (D.move_eval _ _ _ _ _ _).mp edge
    exact ⟨(D.lt_numeral_iff s.state 380).mpr ⟨q.val,q.isLt,state⟩,
      (D.tick_move s q read state input).trans moved.symm⟩
  · rintro ⟨guard,moved⟩
    obtain ⟨q,hq,hState⟩ := (D.lt_numeral_iff _ _).mp guard
    obtain ⟨read,input⟩ := D.bit_read s.right
    let i : Fin 380 := ⟨q,hq⟩
    refine ⟨i,D.numeral_value.mpr (congrArg Subtype.val hState),read,?_⟩
    rw [rowShape]
    exact (D.move_eval _ _ _ _ _ _).mpr ⟨input,moved.symm.trans (D.tick_move s i read hState input)⟩

end PalomarI3380.Logic.Expanded.OmegaDomain
