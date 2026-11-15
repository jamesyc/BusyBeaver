module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 3136 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 3140 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 3144 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 3148 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 3152 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 3156 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 3160 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 3164 4 = true := by decide +kernel

theorem checked098 : blockCheck fuelLimit 3136 32 = true :=
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
