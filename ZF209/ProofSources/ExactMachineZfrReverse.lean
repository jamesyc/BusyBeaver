module
public import Machine209Refutation
public import FoundationReverseCalibration
@[expose] public section
namespace ZF209
/-- Literal blank-tape 209-state machine halting yields a proof of bottom in
the exact ZFR presentation. External proof existence, not PA internalization. -/
theorem literal209_halts_to_zfr_refutation
 (h : M6.Zip.Halts M209.literal (M6.Zip.zc 0 [] [])) : ZFR.ZfrProvable 0 :=
 ZFR.FoundationBridge.exact_reverse_calibration
  (C209Search.literal209_halts_iff_C209_refutation.mp h)

end ZF209
