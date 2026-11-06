import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part6
open PA215.Contracts PA215.Census

def original1638 : RawOriginal := C012.records[102]'(by decide)
theorem original_id1638 : original1638.index = 1638 := by decide

def c1638 : Contract := original1638.toContract.get (by decide)
theorem binding1638 : original1638.toContract = some c1638 := rfl

theorem checked1638 : check 4000 c1638 = true := by decide

def original1639 : RawOriginal := C012.records[103]'(by decide)
theorem original_id1639 : original1639.index = 1639 := by decide

def c1639 : Contract := original1639.toContract.get (by decide)
theorem binding1639 : original1639.toContract = some c1639 := rfl

theorem checked1639 : check 4000 c1639 = true := by decide

def original1640 : RawOriginal := C012.records[104]'(by decide)
theorem original_id1640 : original1640.index = 1640 := by decide

def c1640 : Contract := original1640.toContract.get (by decide)
theorem binding1640 : original1640.toContract = some c1640 := rfl

theorem checked1640 : check 4000 c1640 = true := by decide

def original1641 : RawOriginal := C012.records[105]'(by decide)
theorem original_id1641 : original1641.index = 1641 := by decide

def c1641 : Contract := original1641.toContract.get (by decide)
theorem binding1641 : original1641.toContract = some c1641 := rfl

theorem checked1641 : check 4000 c1641 = true := by decide

def original1642 : RawOriginal := C012.records[106]'(by decide)
theorem original_id1642 : original1642.index = 1642 := by decide

def c1642 : Contract := original1642.toContract.get (by decide)
theorem binding1642 : original1642.toContract = some c1642 := rfl

theorem checked1642 : check 4000 c1642 = true := by decide

def original1643 : RawOriginal := C012.records[107]'(by decide)
theorem original_id1643 : original1643.index = 1643 := by decide

def c1643 : Contract := original1643.toContract.get (by decide)
theorem binding1643 : original1643.toContract = some c1643 := rfl

theorem checked1643 : check 4000 c1643 = true := by decide

def original1644 : RawOriginal := C012.records[108]'(by decide)
theorem original_id1644 : original1644.index = 1644 := by decide

def c1644 : Contract := original1644.toContract.get (by decide)
theorem binding1644 : original1644.toContract = some c1644 := rfl

theorem checked1644 : check 4000 c1644 = true := by decide

def original1645 : RawOriginal := C012.records[109]'(by decide)
theorem original_id1645 : original1645.index = 1645 := by decide

def c1645 : Contract := original1645.toContract.get (by decide)
theorem binding1645 : original1645.toContract = some c1645 := rfl

theorem checked1645 : check 4000 c1645 = true := by decide

def original1646 : RawOriginal := C012.records[110]'(by decide)
theorem original_id1646 : original1646.index = 1646 := by decide

def c1646 : Contract := original1646.toContract.get (by decide)
theorem binding1646 : original1646.toContract = some c1646 := rfl

theorem checked1646 : check 4000 c1646 = true := by decide

def original1647 : RawOriginal := C012.records[111]'(by decide)
theorem original_id1647 : original1647.index = 1647 := by decide

def c1647 : Contract := original1647.toContract.get (by decide)
theorem binding1647 : original1647.toContract = some c1647 := rfl

theorem checked1647 : check 4000 c1647 = true := by decide

def original1648 : RawOriginal := C012.records[112]'(by decide)
theorem original_id1648 : original1648.index = 1648 := by decide

def c1648 : Contract := original1648.toContract.get (by decide)
theorem binding1648 : original1648.toContract = some c1648 := rfl

theorem checked1648 : check 4000 c1648 = true := by decide

def original1649 : RawOriginal := C012.records[113]'(by decide)
theorem original_id1649 : original1649.index = 1649 := by decide

def c1649 : Contract := original1649.toContract.get (by decide)
theorem binding1649 : original1649.toContract = some c1649 := rfl

theorem checked1649 : check 4000 c1649 = true := by decide

def original1650 : RawOriginal := C012.records[114]'(by decide)
theorem original_id1650 : original1650.index = 1650 := by decide

def c1650 : Contract := original1650.toContract.get (by decide)
theorem binding1650 : original1650.toContract = some c1650 := rfl

theorem checked1650 : check 4000 c1650 = true := by decide

def original1651 : RawOriginal := C012.records[115]'(by decide)
theorem original_id1651 : original1651.index = 1651 := by decide

def c1651 : Contract := original1651.toContract.get (by decide)
theorem binding1651 : original1651.toContract = some c1651 := rfl

theorem checked1651 : check 4000 c1651 = true := by decide

def original1652 : RawOriginal := C012.records[116]'(by decide)
theorem original_id1652 : original1652.index = 1652 := by decide

def c1652 : Contract := original1652.toContract.get (by decide)
theorem binding1652 : original1652.toContract = some c1652 := rfl

theorem checked1652 : check 4000 c1652 = true := by decide

def original1653 : RawOriginal := C012.records[117]'(by decide)
theorem original_id1653 : original1653.index = 1653 := by decide

def c1653 : Contract := original1653.toContract.get (by decide)
theorem binding1653 : original1653.toContract = some c1653 := rfl

theorem checked1653 : check 4000 c1653 = true := by decide

def records : List Certified := [
  ⟨1638, c1638, 4000, checked1638⟩,
  ⟨1639, c1639, 4000, checked1639⟩,
  ⟨1640, c1640, 4000, checked1640⟩,
  ⟨1641, c1641, 4000, checked1641⟩,
  ⟨1642, c1642, 4000, checked1642⟩,
  ⟨1643, c1643, 4000, checked1643⟩,
  ⟨1644, c1644, 4000, checked1644⟩,
  ⟨1645, c1645, 4000, checked1645⟩,
  ⟨1646, c1646, 4000, checked1646⟩,
  ⟨1647, c1647, 4000, checked1647⟩,
  ⟨1648, c1648, 4000, checked1648⟩,
  ⟨1649, c1649, 4000, checked1649⟩,
  ⟨1650, c1650, 4000, checked1650⟩,
  ⟨1651, c1651, 4000, checked1651⟩,
  ⟨1652, c1652, 4000, checked1652⟩,
  ⟨1653, c1653, 4000, checked1653⟩]

end PA215.ContractShards.Shard012Part6
