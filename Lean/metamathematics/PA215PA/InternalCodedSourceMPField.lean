import PA215PA.InternalCodedSourceUnpairRelocation
import PA215.Source.MPField
namespace PA215.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Actual MP offset reader: L is decoded into its tail and its head is added
to D. The accumulator is not silently reset. -/
theorem actual_mp_field (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode 3805 (unpairStore 8 6 7 xs n 0 0))
      (stateCode 3819 (unpairFullEnd 8 6 7 4 xs n)) := by
  exact unpair_relocated Source.MPField.relocation Source.MPField.bound (by decide) n xs hv
lemma mp_field_effect (n xs : V) (hv : ValidStore xs) :
    registers (unpairFullEnd 8 6 7 4 xs n)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
        (PhysicalRegisters.write (registers xs) 8 (decodeRight n)) 6 0) 7 0) 4 (registers xs 4+decodeLeft n) :=
  unpairFullEnd_effect 8 6 7 4 xs n hv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
#print axioms actual_mp_field
#print axioms mp_field_effect
end PA215.PA.InternalTrace.CodedSource
