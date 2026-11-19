module
public import Machine207Refutation
public import FoundationReverseCalibration
@[expose] public section
namespace ZF207
/-- Literal blank-tape 207-state machine halting yields a proof of bottom in
the exact ZFR presentation. External proof existence, not PA internalization. -/
theorem literal207_halts_to_zfr_refutation
 (h : M6.Zip.Halts M207.literal (M6.Zip.zc 0 [] [])) : ZFR.ZfrProvable 0 :=
 ZFR.FoundationBridge.exact_reverse_calibration
  (C207Search.literal207_halts_iff_C207_refutation.mp h)

end ZF207
