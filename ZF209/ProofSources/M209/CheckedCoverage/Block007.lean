module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 224 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 228 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 232 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 236 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 240 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 244 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 248 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 252 4 = true := by decide +kernel

theorem checked007 : blockCheck fuelLimit 224 32 = true :=
  (append_checks
    (append_checks
      (append_checks
        checkedPart0
        checkedPart1)
      (append_checks
        checkedPart2
        checkedPart3))
    (append_checks
      (append_checks
        checkedPart4
        checkedPart5)
      (append_checks
        checkedPart6
        checkedPart7)))

end M209.Source.CheckedCoverage
