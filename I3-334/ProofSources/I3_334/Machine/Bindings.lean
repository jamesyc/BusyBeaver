module
public import I3_334.Literal
@[expose] public section

namespace PalomarI3334

open PalomarI3380

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem literal_binding :
    machine.workingStates = 334 ∧ literal.size = 668 ∧
    (literal.toList.zipIdx.all fun (row, i) => machine.row (i / 2) (i % 2) == row) = true ∧
    (literal.toList.all fun row => row / 4 ≤ 334) = true ∧
    (literal.toList.zipIdx.filter fun (row, _) => row / 4 == 334) = [(4 * 334 + 3, 379)] := by
  decide +kernel

end PalomarI3334
