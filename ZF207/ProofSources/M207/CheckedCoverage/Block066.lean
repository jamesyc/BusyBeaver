module
public import M207.CheckedCoverage

@[expose] public section

namespace M207.Source.CheckedCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

private theorem checkedPart0 : blockCheck fuelLimit 2112 4 = true := by decide +kernel
private theorem checkedPart1 : blockCheck fuelLimit 2116 4 = true := by decide +kernel
private theorem checkedPart2 : blockCheck fuelLimit 2120 4 = true := by decide +kernel
private theorem checkedPart3 : blockCheck fuelLimit 2124 4 = true := by decide +kernel
private theorem checkedPart4 : blockCheck fuelLimit 2128 4 = true := by decide +kernel
private theorem checkedPart5 : blockCheck fuelLimit 2132 4 = true := by decide +kernel
private theorem checkedPart6 : blockCheck fuelLimit 2136 4 = true := by decide +kernel
private theorem checkedPart7 : blockCheck fuelLimit 2140 4 = true := by decide +kernel

theorem checked066 : blockCheck fuelLimit 2112 32 = true :=
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
