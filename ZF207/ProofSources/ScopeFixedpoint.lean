module
public import DirectDepthShift
public import ExecutableZFAxioms
@[expose] public section
namespace RosserDirect.ScopeFixedpoint

theorem index_fixed (n i : Nat) : ZFR.sourceShiftIndex n i = i ↔ i < n := by
 unfold ZFR.sourceShiftIndex
 split_ifs <;> omega

theorem formula_fixed (f : ZFR.Formula) (n : Nat) :
 DepthShift.shifted n f = f ↔ ZFR.Bound f n := by
 induction f generalizing n with
 | bot => simp [DepthShift.shifted,ZFR.rename,ZFR.Bound]
 | mem i j => simp [DepthShift.shifted,ZFR.rename,ZFR.Bound,index_fixed]
 | eq i j => simp [DepthShift.shifted,ZFR.rename,ZFR.Bound,index_fixed]
 | and p q hp hq => simp_all [DepthShift.shifted,ZFR.rename,ZFR.Bound]
 | or p q hp hq => simp_all [DepthShift.shifted,ZFR.rename,ZFR.Bound]
 | imp p q hp hq => simp_all [DepthShift.shifted,ZFR.rename,ZFR.Bound]
 | all p hp => simpa [DepthShift.shifted,ZFR.rename,ZFR.sourceShiftIndex_lift,ZFR.Bound] using hp (n+1)
 | ex p hp => simpa [DepthShift.shifted,ZFR.rename,ZFR.sourceShiftIndex_lift,ZFR.Bound] using hp (n+1)

end RosserDirect.ScopeFixedpoint
