module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 1152 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 1156 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 1160 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 1164 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 1168 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 1172 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 1176 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 1180 4 = true := by decide +kernel

theorem checked036 : blockCheck fuelLimit 1152 32 = true :=
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
