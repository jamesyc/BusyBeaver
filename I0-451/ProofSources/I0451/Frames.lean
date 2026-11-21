module
public import I0451.Boot
public import I0451.RegisterAccess

/-! Register frames use a slot measured from the decoder root to the
first encoded register. Explicit trailing zeros in an address are
interchangeable with the same number of gap cells. -/
@[expose] public section
namespace I0451.Runtime

theorem pack_value (word : List Bool) (tail : Nat) :
    pack word tail = pack word 0 + 2 ^ word.length * tail := by
  induction word with
  | nil => simp
  | cons b word ih =>
    simp only [pack_cons, List.length_cons, ih]
    simp [push, Nat.pow_succ', Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem pack_zero_word (n : Nat) : pack (List.replicate n false) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, push, ih]

theorem pack_slot (word : List Bool) (gap tail : Nat) :
    pack word (pack (List.replicate gap false) tail) =
      pack word 0 + 2 ^ (word.length + gap) * tail := by
  rw [pack_value word, pack_value (List.replicate gap false), pack_zero_word]
  simp [Nat.pow_add, Nat.mul_assoc]

theorem frame_equal {x y : List Bool} {a b : Nat} (ip : pack x 0 = pack y 0)
    (slot : x.length + a = y.length + b) (regs : List Nat) :
    frame x a regs = frame y b regs := by
  simp only [frame, pack_slot, slot, ip]

structure RegisterFrame where
  word : List Bool
  slot : Nat
  regs : List Nat
  deriving DecidableEq, Repr

/-- View an abstract frame on the literal tape. -/
def RegisterFrame.tape (f : RegisterFrame) : Config :=
  frame f.word (f.slot - f.word.length) f.regs

/-- The 192 fixed register blocks used to establish the marker and the
initial shape of the selectable register file. -/
def fixedBlocks : List Nat := List.replicate 132 0 ++ [1] ++ List.replicate 59 0

/-- At the first decoder entry all nine live registers are zero. -/
def initialFrame : RegisterFrame := ⟨[], 19, fixedBlocks ++ List.replicate 9 0⟩

theorem boot_register_frame : bootFrame = initialFrame.tape := by
  decide +kernel

theorem blank_reaches_initial_frame : Reaches literal (blank 0) initialFrame.tape :=
  ⟨39753, boot_register_frame ▸ literal_boot⟩

/-- A successful path reads the address with zero padding. The parsed
word has the same packed address, so it may be used as the explicit
part of the physical tape. -/
theorem RegisterFrame.tape_decoded (state : RegisterFrame) (result : Decoder.Decoded)
    (parsed : Decoder.decode 94 root true false (pack state.word 0) = some result)
    (wordFits : state.word.length ≤ state.slot) (pathFits : result.word.length ≤ state.slot)
    (noStray : result.rest = 0) :
    state.tape = frame result.word (state.slot - result.word.length) state.regs := by
  have h := (Decoder.decode_sound parsed).1
  rw [noStray] at h
  exact frame_equal h (by omega) state.regs

end I0451.Runtime
