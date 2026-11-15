module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 2560 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 2564 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 2568 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 2572 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 2576 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 2580 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 2584 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 2588 4 = true := by decide +kernel

theorem checked080 : blockCheck fuelLimit 2560 32 = true :=
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
