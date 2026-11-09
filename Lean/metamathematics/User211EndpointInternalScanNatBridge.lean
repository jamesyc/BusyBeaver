/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
import PA215PA.Theory
import User211PAInternalScanBits
import User211EndpointZipNatTape

namespace PA211.UserCandidate.PA.InternalTrace.ScanBits
open PA215 PA215.PA
/-- Standard-model calibration to the existing zipper's binary stack encoding.
This lemma calibrates the code; the PA scan proof uses model induction separately. -/
theorem repeat_bits (n : Nat) (b : Bool) (tail : List Bool) :
    repeatBits n b.toNat (ZipNatTape.bits tail) =
      ZipNatTape.bits (List.replicate n b ++ tail) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [repeat_succ,List.replicate_succ,ZipNatTape.bits_cons,NatTape.push,ih]
#print axioms repeat_bits
end PA211.UserCandidate.PA.InternalTrace.ScanBits

