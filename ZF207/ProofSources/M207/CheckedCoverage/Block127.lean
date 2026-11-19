module
public import M207.CheckedCoverage

@[expose] public section

namespace M207.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 4064 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 4068 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 4072 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 4076 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 4080 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 4084 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 4088 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 4092 4 = true := by decide +kernel

theorem checked127 : blockCheck fuelLimit 4064 32 = true :=
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
