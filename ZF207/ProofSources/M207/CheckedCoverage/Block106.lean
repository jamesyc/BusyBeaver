module
public import M207.CheckedCoverage

@[expose] public section

namespace M207.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 3392 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 3396 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 3400 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 3404 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 3408 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 3412 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 3416 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 3420 4 = true := by decide +kernel

theorem checked106 : blockCheck fuelLimit 3392 32 = true :=
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

end M207.Source.CheckedCoverage
