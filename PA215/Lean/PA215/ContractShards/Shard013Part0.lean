import PA215.CertifiedContracts
import PA215.Census.C013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013Part0
open PA215.Contracts PA215.Census

def original1670 : RawOriginal := C013.records[6]'(by decide)
theorem original_id1670 : original1670.index = 1670 := by decide

def c1670 : Contract := original1670.toContract.get (by decide)
theorem binding1670 : original1670.toContract = some c1670 := rfl

theorem checked1670 : check 4000 c1670 = true := by decide

def original1671 : RawOriginal := C013.records[7]'(by decide)
theorem original_id1671 : original1671.index = 1671 := by decide

def c1671 : Contract := original1671.toContract.get (by decide)
theorem binding1671 : original1671.toContract = some c1671 := rfl

theorem checked1671 : check 4000 c1671 = true := by decide

def original1672 : RawOriginal := C013.records[8]'(by decide)
theorem original_id1672 : original1672.index = 1672 := by decide

def c1672 : Contract := original1672.toContract.get (by decide)
theorem binding1672 : original1672.toContract = some c1672 := rfl

theorem checked1672 : check 4000 c1672 = true := by decide

def original1673 : RawOriginal := C013.records[9]'(by decide)
theorem original_id1673 : original1673.index = 1673 := by decide

def c1673 : Contract := original1673.toContract.get (by decide)
theorem binding1673 : original1673.toContract = some c1673 := rfl

theorem checked1673 : check 4000 c1673 = true := by decide

def original1674 : RawOriginal := C013.records[10]'(by decide)
theorem original_id1674 : original1674.index = 1674 := by decide

def c1674 : Contract := original1674.toContract.get (by decide)
theorem binding1674 : original1674.toContract = some c1674 := rfl

theorem checked1674 : check 4000 c1674 = true := by decide

def original1675 : RawOriginal := C013.records[11]'(by decide)
theorem original_id1675 : original1675.index = 1675 := by decide

def c1675 : Contract := original1675.toContract.get (by decide)
theorem binding1675 : original1675.toContract = some c1675 := rfl

theorem checked1675 : check 4000 c1675 = true := by decide

def original1676 : RawOriginal := C013.records[12]'(by decide)
theorem original_id1676 : original1676.index = 1676 := by decide

def c1676 : Contract := original1676.toContract.get (by decide)
theorem binding1676 : original1676.toContract = some c1676 := rfl

theorem checked1676 : check 4000 c1676 = true := by decide

def original1677 : RawOriginal := C013.records[13]'(by decide)
theorem original_id1677 : original1677.index = 1677 := by decide

def c1677 : Contract := original1677.toContract.get (by decide)
theorem binding1677 : original1677.toContract = some c1677 := rfl

theorem checked1677 : check 4000 c1677 = true := by decide

def original1678 : RawOriginal := C013.records[14]'(by decide)
theorem original_id1678 : original1678.index = 1678 := by decide

def c1678 : Contract := original1678.toContract.get (by decide)
theorem binding1678 : original1678.toContract = some c1678 := rfl

theorem checked1678 : check 4000 c1678 = true := by decide

def original1679 : RawOriginal := C013.records[15]'(by decide)
theorem original_id1679 : original1679.index = 1679 := by decide

def c1679 : Contract := original1679.toContract.get (by decide)
theorem binding1679 : original1679.toContract = some c1679 := rfl

theorem checked1679 : check 4000 c1679 = true := by decide

def original1680 : RawOriginal := C013.records[16]'(by decide)
theorem original_id1680 : original1680.index = 1680 := by decide

def c1680 : Contract := original1680.toContract.get (by decide)
theorem binding1680 : original1680.toContract = some c1680 := rfl

theorem checked1680 : check 4000 c1680 = true := by decide

def original1681 : RawOriginal := C013.records[17]'(by decide)
theorem original_id1681 : original1681.index = 1681 := by decide

def c1681 : Contract := original1681.toContract.get (by decide)
theorem binding1681 : original1681.toContract = some c1681 := rfl

theorem checked1681 : check 4000 c1681 = true := by decide

def original1682 : RawOriginal := C013.records[18]'(by decide)
theorem original_id1682 : original1682.index = 1682 := by decide

def c1682 : Contract := original1682.toContract.get (by decide)
theorem binding1682 : original1682.toContract = some c1682 := rfl

theorem checked1682 : check 4000 c1682 = true := by decide

def original1683 : RawOriginal := C013.records[19]'(by decide)
theorem original_id1683 : original1683.index = 1683 := by decide

def c1683 : Contract := original1683.toContract.get (by decide)
theorem binding1683 : original1683.toContract = some c1683 := rfl

theorem checked1683 : check 4000 c1683 = true := by decide

def original1684 : RawOriginal := C013.records[20]'(by decide)
theorem original_id1684 : original1684.index = 1684 := by decide

def c1684 : Contract := original1684.toContract.get (by decide)
theorem binding1684 : original1684.toContract = some c1684 := rfl

theorem checked1684 : check 4000 c1684 = true := by decide

def original1685 : RawOriginal := C013.records[21]'(by decide)
theorem original_id1685 : original1685.index = 1685 := by decide

def c1685 : Contract := original1685.toContract.get (by decide)
theorem binding1685 : original1685.toContract = some c1685 := rfl

theorem checked1685 : check 4000 c1685 = true := by decide

def records : List Certified := [
  ⟨1670, c1670, 4000, checked1670⟩,
  ⟨1671, c1671, 4000, checked1671⟩,
  ⟨1672, c1672, 4000, checked1672⟩,
  ⟨1673, c1673, 4000, checked1673⟩,
  ⟨1674, c1674, 4000, checked1674⟩,
  ⟨1675, c1675, 4000, checked1675⟩,
  ⟨1676, c1676, 4000, checked1676⟩,
  ⟨1677, c1677, 4000, checked1677⟩,
  ⟨1678, c1678, 4000, checked1678⟩,
  ⟨1679, c1679, 4000, checked1679⟩,
  ⟨1680, c1680, 4000, checked1680⟩,
  ⟨1681, c1681, 4000, checked1681⟩,
  ⟨1682, c1682, 4000, checked1682⟩,
  ⟨1683, c1683, 4000, checked1683⟩,
  ⟨1684, c1684, 4000, checked1684⟩,
  ⟨1685, c1685, 4000, checked1685⟩]

end PA215.ContractShards.Shard013Part0
