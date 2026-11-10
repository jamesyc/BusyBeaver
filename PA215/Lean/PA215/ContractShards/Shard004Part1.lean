import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part1
open PA215.Contracts PA215.Census

def original534 : RawOriginal := C004.records[22]'(by decide)
theorem original_id534 : original534.index = 534 := by decide

def c534 : Contract := original534.toContract.get (by decide)
theorem binding534 : original534.toContract = some c534 := rfl

theorem checked534 : check 4000 c534 = true := by decide

def original535 : RawOriginal := C004.records[23]'(by decide)
theorem original_id535 : original535.index = 535 := by decide

def c535 : Contract := original535.toContract.get (by decide)
theorem binding535 : original535.toContract = some c535 := rfl

theorem checked535 : check 4000 c535 = true := by decide

def original536 : RawOriginal := C004.records[24]'(by decide)
theorem original_id536 : original536.index = 536 := by decide

def c536 : Contract := original536.toContract.get (by decide)
theorem binding536 : original536.toContract = some c536 := rfl

theorem checked536 : check 4000 c536 = true := by decide

def original537 : RawOriginal := C004.records[25]'(by decide)
theorem original_id537 : original537.index = 537 := by decide

def c537 : Contract := original537.toContract.get (by decide)
theorem binding537 : original537.toContract = some c537 := rfl

theorem checked537 : check 4000 c537 = true := by decide

def original538 : RawOriginal := C004.records[26]'(by decide)
theorem original_id538 : original538.index = 538 := by decide

def c538 : Contract := original538.toContract.get (by decide)
theorem binding538 : original538.toContract = some c538 := rfl

theorem checked538 : check 4000 c538 = true := by decide

def original539 : RawOriginal := C004.records[27]'(by decide)
theorem original_id539 : original539.index = 539 := by decide

def c539 : Contract := original539.toContract.get (by decide)
theorem binding539 : original539.toContract = some c539 := rfl

theorem checked539 : check 4000 c539 = true := by decide

def original540 : RawOriginal := C004.records[28]'(by decide)
theorem original_id540 : original540.index = 540 := by decide

def c540 : Contract := original540.toContract.get (by decide)
theorem binding540 : original540.toContract = some c540 := rfl

theorem checked540 : check 4000 c540 = true := by decide

def original541 : RawOriginal := C004.records[29]'(by decide)
theorem original_id541 : original541.index = 541 := by decide

def c541 : Contract := original541.toContract.get (by decide)
theorem binding541 : original541.toContract = some c541 := rfl

theorem checked541 : check 4000 c541 = true := by decide

def original542 : RawOriginal := C004.records[30]'(by decide)
theorem original_id542 : original542.index = 542 := by decide

def c542 : Contract := original542.toContract.get (by decide)
theorem binding542 : original542.toContract = some c542 := rfl

theorem checked542 : check 4000 c542 = true := by decide

def original543 : RawOriginal := C004.records[31]'(by decide)
theorem original_id543 : original543.index = 543 := by decide

def c543 : Contract := original543.toContract.get (by decide)
theorem binding543 : original543.toContract = some c543 := rfl

theorem checked543 : check 4000 c543 = true := by decide

def original544 : RawOriginal := C004.records[32]'(by decide)
theorem original_id544 : original544.index = 544 := by decide

def c544 : Contract := original544.toContract.get (by decide)
theorem binding544 : original544.toContract = some c544 := rfl

theorem checked544 : check 4000 c544 = true := by decide

def original545 : RawOriginal := C004.records[33]'(by decide)
theorem original_id545 : original545.index = 545 := by decide

def c545 : Contract := original545.toContract.get (by decide)
theorem binding545 : original545.toContract = some c545 := rfl

theorem checked545 : check 4000 c545 = true := by decide

def original546 : RawOriginal := C004.records[34]'(by decide)
theorem original_id546 : original546.index = 546 := by decide

def c546 : Contract := original546.toContract.get (by decide)
theorem binding546 : original546.toContract = some c546 := rfl

theorem checked546 : check 4000 c546 = true := by decide

def original547 : RawOriginal := C004.records[35]'(by decide)
theorem original_id547 : original547.index = 547 := by decide

def c547 : Contract := original547.toContract.get (by decide)
theorem binding547 : original547.toContract = some c547 := rfl

theorem checked547 : check 4000 c547 = true := by decide

def original548 : RawOriginal := C004.records[36]'(by decide)
theorem original_id548 : original548.index = 548 := by decide

def c548 : Contract := original548.toContract.get (by decide)
theorem binding548 : original548.toContract = some c548 := rfl

theorem checked548 : check 4000 c548 = true := by decide

def original549 : RawOriginal := C004.records[37]'(by decide)
theorem original_id549 : original549.index = 549 := by decide

def c549 : Contract := original549.toContract.get (by decide)
theorem binding549 : original549.toContract = some c549 := rfl

theorem checked549 : check 4000 c549 = true := by decide

def records : List Certified := [
  ⟨534, c534, 4000, checked534⟩,
  ⟨535, c535, 4000, checked535⟩,
  ⟨536, c536, 4000, checked536⟩,
  ⟨537, c537, 4000, checked537⟩,
  ⟨538, c538, 4000, checked538⟩,
  ⟨539, c539, 4000, checked539⟩,
  ⟨540, c540, 4000, checked540⟩,
  ⟨541, c541, 4000, checked541⟩,
  ⟨542, c542, 4000, checked542⟩,
  ⟨543, c543, 4000, checked543⟩,
  ⟨544, c544, 4000, checked544⟩,
  ⟨545, c545, 4000, checked545⟩,
  ⟨546, c546, 4000, checked546⟩,
  ⟨547, c547, 4000, checked547⟩,
  ⟨548, c548, 4000, checked548⟩,
  ⟨549, c549, 4000, checked549⟩]

end PA215.ContractShards.Shard004Part1
