module
public import I0451.ArithmeticAccess
public import I0451.StandardPrefix

/-! The model-valued register representation agrees with the actual
literal startup frame on its standard initial contents. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelPush_cast (b : Bool) (tail : Nat) :
    modelPush b (tail : V) = (I0451.push b tail : V) := by
  simp [modelPush, I0451.push, add_comm]

theorem modelPack_cast (word : List Bool) (tail : Nat) :
    modelPack word (tail : V) = (pack word tail : V) := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    rw [modelPack_cons, pack_cons, ih, modelPush_cast]

theorem modelBlocks_cast (regs : List Nat) (tail : Nat) :
    modelBlocks (regs.map fun n : Nat => (↑n : V)) (tail : V) = (pack (blocks regs) tail : V) := by
  induction regs with
  | nil => rfl
  | cons x regs ih =>
    simp only [List.map_cons, modelBlocks, blocks, pack_append, pack_cons, ih, modelPush_cast]
    rw [← Nat.cast_succ, modelRepeat_nat, modelPack_cast]

theorem modelConfig_cast (state left right : Nat) :
    modelConfig state (left : V) (right : V) =
      (encodeConfig (⟨state,left,right⟩ : Config) : V) := by
  unfold modelConfig encodeConfig
  simp only [nat_cast_pair]

theorem modelFrame_cast (word : List Bool) (gap : Nat) (regs : List Nat) :
    modelFrame word (gap : V) (regs.map fun n : Nat => (↑n : V)) = (encodeConfig (frame word gap regs) : V) := by
  unfold modelFrame frame
  have blocksEq := modelBlocks_cast (V := V) regs 0
  simp only [Nat.cast_zero] at blocksEq
  rw [← modelConfig_cast, blocksEq, modelRepeat_nat, modelPack_cast, modelPack_cast]
  rw [Nat.cast_one]

theorem modelPack_value (word : List Bool) (tail : V) :
    modelPack word tail = (pack word 0 : V) + modelRepeat false (word.length : V) tail := by
  induction word with
  | nil => simp
  | cons b word ih =>
    simp only [modelPack_cons, ih, modelPush, pack_cons, I0451.push, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, List.length_cons, Nat.cast_succ, modelRepeat_succ, Bool.toNat_false,
      Nat.cast_zero, mul_add, add_zero]
    ac_rfl

theorem modelFrame_equal {a b : List Bool} {gapA gapB : V}
    (packed : pack a 0 = pack b 0) (slot : gapA + (a.length : V) = gapB + (b.length : V))
    (regs : List V) :
    modelFrame a gapA regs = modelFrame b gapB regs := by
  simp only [modelFrame, modelPack_value, ← modelRepeat_add, packed, slot]

theorem modelFrame_decoded {word : List Bool} {slot : V} {decoded : Decoder.Decoded}
    (parsed : Decoder.decode 94 root true false (pack word 0) = some decoded)
    (wordFits : (word.length : V) ≤ slot) (pathFits : (decoded.word.length : V) ≤ slot)
    (noStray : decoded.rest = 0) (regs : List V) :
    modelFrame word (slot - (word.length : V)) regs =
      modelFrame decoded.word (slot - (decoded.word.length : V)) regs := by
  have packed := (Decoder.decode_sound parsed).1
  rw [noStray] at packed
  exact modelFrame_equal packed
    ((sub_add_self_of_le wordFits).trans (sub_add_self_of_le pathFits).symm) regs

theorem literal_halts_from_registers :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) ↔
      ∃ n : V, Terminal literal (trace literal n
        (modelFrame commandBoundary.word ((commandBoundary.slot - commandBoundary.word.length : Nat) : V)
          (commandBoundary.regs.map fun x : Nat => (↑x : V)))) := by
  rw [modelFrame_cast]
  exact literal_halts_from_boundary

end I0451.Arithmetization
