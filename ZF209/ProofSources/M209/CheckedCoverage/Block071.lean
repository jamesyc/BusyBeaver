module
public import M209.CheckedCoverage

@[expose] public section

namespace M209.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 2272 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 2276 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 2280 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 2284 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 2288 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 2292 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 2296 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 2300 4 = true := by decide +kernel

theorem checked071 : blockCheck fuelLimit 2272 32 = true :=
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
