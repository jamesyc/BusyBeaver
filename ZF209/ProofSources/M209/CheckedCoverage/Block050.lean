module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 1600 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 1604 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 1608 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 1612 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 1616 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 1620 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 1624 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 1628 4 = true := by decide +kernel

theorem checked050 : blockCheck fuelLimit 1600 32 = true :=
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
