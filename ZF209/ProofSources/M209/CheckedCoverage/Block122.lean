module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 3904 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 3908 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 3912 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 3916 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 3920 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 3924 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 3928 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 3932 4 = true := by decide +kernel

theorem checked122 : blockCheck fuelLimit 3904 32 = true :=
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
