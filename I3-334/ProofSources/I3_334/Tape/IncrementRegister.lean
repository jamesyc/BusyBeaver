module
public import I3_334.Tape.StockScans
public import I3_334.Machine.ReferenceData
public import I3_334.Literal
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure IncrementRows (m : Machine) (lead scan separator : Nat) : Prop where
  leadingZero : Row m lead false false true lead
  leadingOne : Row m lead true true true scan
  scanOne : Row m scan true true true scan
  scanZero : Row m scan false false true separator
  nextRegister : Row m separator true true true scan
  extendRegister : Row m separator false true false 46
  returnRows : ReturnRows m 46 62 80 33

private theorem inc334 : IncrementRows machine 50 66 84 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> decide +kernel

noncomputable def selectedFile (a : M) (before : List M) (v rest : M) : M :=
  registers (a :: before) (pushBit false (pushBit false (repeatBit true (v + 1) rest)))

noncomputable def incrementedFile (a : M) (before : List M) (v rest : M) : M :=
  registers (a :: before) (pushBit false (repeatBit true (v + 2) rest))

private theorem increment_after_marker {m : Machine} {lead scan separator : Nat}
    (rows : IncrementRows m lead scan separator) (leftTail gap a : M) (before : List M) (v rest : M) :
    Reaches m
      (cell lead (pushBit true leftTail) (repeatBit false (gap+1) (selectedFile a before v rest)))
      (fromLeft 33 leftTail (pushBit false (repeatBit false (gap+1) (incrementedFile a before v rest)))) := by
  have pass := scanRight rows.leadingZero (gap + 1) (pushBit true leftTail) (selectedFile a before v rest)
  have selected := scanFirstMarked rows.leadingZero rows.leadingOne rows.scanOne rows.scanZero
    rows.nextRegister rows.extendRegister a before (repeatBit false (gap + 1) (pushBit true leftTail))
    (repeatBit true (v + 1) rest)
  have finish := scanReturn rows.returnRows (a :: before).reverse gap leftTail
    (pushBit true (repeatBit true (v + 1) rest))
  have replay := pass.trans (selected.trans finish)
  simpa only [selectedFile, incrementedFile, List.reverse_reverse, ← repeatBit_succ,
    add_assoc, one_add_one_eq_two] using replay

/-- The reference increment writes a temporary return marker before scanning. -/
theorem referenceIncrement (left gap a : M) (before : List M) (v rest : M) :
    Reaches decoderReference
      (cell 50 left (pushBit false (repeatBit false (gap+1) (selectedFile a before v rest))))
      (fromLeft 33 left (pushBit false (repeatBit false (gap+1) (incrementedFile a before v rest)))) := by
  have rows : IncrementRows decoderReference 66 84 100 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> decide +kernel
  have mark := right (show Row decoderReference 50 false true true 66 by decide +kernel) left
    (repeatBit false (gap+1) (selectedFile a before v rest))
  exact mark.trans (increment_after_marker rows left gap a before v rest)

/-- On the marker-free literal, the last selection bit is itself the
return marker. Erasing it contributes one zero to the available gap. -/
theorem literalIncrement (left gap a : M) (before : List M) (v rest : M) :
    Reaches machine
      (cell 50 (pushBit true left) (repeatBit false (gap+2) (selectedFile a before v rest)))
      (fromLeft 33 left (repeatBit false (gap+3) (incrementedFile a before v rest))) := by
  have one : gap+2 = (gap+1)+1 := by rw [add_assoc, one_add_one_eq_two]
  have two : gap+3 = (gap+2)+1 := by
    have h : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
    rw [add_assoc,h]
  rw [two, repeatBit_succ, one]
  exact increment_after_marker inc334 left (gap+1) a before v rest

end PalomarI3334.Stock
