module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 4320 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 4324 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 4328 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 4332 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 4336 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 4340 1 = true := by decide +kernel

theorem checked135 : blockCheck fuelLimit 4320 21 = true :=
  (append_checks
    (append_checks
      checkedPart0
      (append_checks
        checkedPart1
        checkedPart2))
    (append_checks
      checkedPart3
      (append_checks
        checkedPart4
        checkedPart5)))

end M209.Source.CheckedCoverage
