module
public import M207.CheckedCoverage

@[expose] public section

namespace M207.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 4160 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 4164 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 4168 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 4172 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 4176 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 4180 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 4184 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 4188 4 = true := by decide +kernel

theorem checked130 : blockCheck fuelLimit 4160 32 = true :=
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
