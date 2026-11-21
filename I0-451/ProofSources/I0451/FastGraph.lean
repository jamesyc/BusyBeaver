module
public import I0451.InstructionGraph

/-! Packed memoization of the arm decoder. Each stored edge is
independently validated against the literal tape transition table. -/
@[expose] public section
namespace I0451.Runtime

def cachedOutgoing (cursor : Cursor) (read : Bool) : Option Edge :=
  if cursor.control ≥ 451 then none
  else
    let index := 8 * cursor.control + 4 * cursor.earlier.toNat +
      2 * cursor.previous.toNat + read.toNat
    let code := (decoderGraph >>> (11 * index)) &&& 2047
    if code = 0 then none
    else if code ≤ 451 then some (.branch ⟨code - 1, read, cursor.previous⟩)
    else if inc : code - 452 < 9 then some (.instruction (.inc ⟨code - 452, inc⟩))
    else if dec : code - 461 < 9 then some (.instruction (.dec ⟨code - 461, dec⟩))
    else match code with
      | 470 => some (.instruction (.break 0))
      | 471 => some (.instruction (.restart 0))
      | 472 => some (.instruction (.restart 1))
      | 473 => some (.instruction (.restart 2))
      | 474 => some (.instruction .halt)
      | _ => none

private def bits := [false, true]

private theorem in_bits (b : Bool) : b ∈ bits := by cases b <;> decide

private def checkArm (cursor : Cursor) (read : Bool) : Bool :=
  match cachedOutgoing cursor read with
  | none => true
  | some e => outgoing cursor read == some e

private def checkArms (states : List Nat) : Bool :=
  states.all fun q => bits.all fun a => bits.all fun b => bits.all fun read =>
    checkArm ⟨q, a, b⟩ read

private theorem checkedLo : checkArms (List.range 226) = true := by decide +kernel
private theorem checkedHi : checkArms (List.range' 226 225) = true := by decide +kernel

theorem cachedOutgoing_sound {cursor : Cursor} {bit : Bool} {edge : Edge}
    (found : cachedOutgoing cursor bit = some edge) : outgoing cursor bit = some edge := by
  obtain ⟨q, a, b⟩ := cursor
  have bound : q < 451 := by
    by_cases h : q < 451
    · exact h
    · simp [cachedOutgoing, Nat.le_of_not_gt h] at found
  have row : bits.all (fun a => bits.all fun b => bits.all fun read =>
      checkArm ⟨q, a, b⟩ read) = true := by
    by_cases lo : q < 226
    · exact List.all_eq_true.mp checkedLo q (List.mem_range.mpr lo)
    · apply List.all_eq_true.mp checkedHi q
      have range : 226 ≤ q ∧ q < 226 + 225 := by omega
      simpa only [List.mem_range'_1] using range
  have prev := List.all_eq_true.mp row a (in_bits a)
  have earlier := List.all_eq_true.mp prev b (in_bits b)
  have arm := List.all_eq_true.mp earlier bit (in_bits bit)
  simpa only [checkArm, found, beq_iff_eq] using arm

end I0451.Runtime
