import PA215PA.Startup.Continuation
import PA215PA.ZipNatTape
import PA215.Source.RootFrame

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.PA.Startup

/-- Complete literal physical file; spare storage is not reset. -/
def startupFile : List Nat := [6, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def startupPath : List Bool := [true, false, true, false, false, true, false, false, true, false, true, true, true, true, false]

def nativeFrame : Zip.Conf :=
  Runtime.conc 0 startupFile (Source.rootFrame startupPath)

theorem full_file_length : startupFile.length = 64 := by decide

theorem nonzero_spare : startupFile[11]? = some 1 := by decide

/-- Literal equality retains every relative bit, including all spare blocks. -/
theorem encode_nativeFrame : ZipNatTape.encode nativeFrame = c064 := by decide

/-- The exact blank machine halts iff the complete native startup frame halts.
This uses relative tape semantics, not an asserted absolute head position. -/
theorem blank_halts_iff_native_frame :
    PA215.Halts PA215.blank ↔ Zip.Halts NativeTable.machine nativeFrame := by
  calc
    PA215.Halts PA215.blank ↔ NatTape.Halts NatTape.blank := NatTape.blank_halts_iff.symm
    _ ↔ NatTape.Halts c064 := blank_halts_iff_final
    _ ↔ NatTape.Halts (ZipNatTape.encode nativeFrame) := by rw [encode_nativeFrame]
    _ ↔ Zip.Halts NativeTable.machine nativeFrame := (ZipNatTape.halts_iff nativeFrame).symm

#print axioms encode_nativeFrame
#print axioms blank_halts_iff_native_frame
end PA215.PA.Startup
