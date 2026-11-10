import PA215.CertifiedContracts
import PA215.Census.C012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard012Part3
open PA215.Contracts PA215.Census

def original1590 : RawOriginal := C012.records[54]'(by decide)
theorem original_id1590 : original1590.index = 1590 := by decide

def c1590 : Contract := original1590.toContract.get (by decide)
theorem binding1590 : original1590.toContract = some c1590 := rfl

theorem checked1590 : check 4000 c1590 = true := by decide

def original1591 : RawOriginal := C012.records[55]'(by decide)
theorem original_id1591 : original1591.index = 1591 := by decide

def c1591 : Contract := original1591.toContract.get (by decide)
theorem binding1591 : original1591.toContract = some c1591 := rfl

theorem checked1591 : check 4000 c1591 = true := by decide

def original1592 : RawOriginal := C012.records[56]'(by decide)
theorem original_id1592 : original1592.index = 1592 := by decide

def c1592 : Contract := original1592.toContract.get (by decide)
theorem binding1592 : original1592.toContract = some c1592 := rfl

theorem checked1592 : check 4000 c1592 = true := by decide

def original1593 : RawOriginal := C012.records[57]'(by decide)
theorem original_id1593 : original1593.index = 1593 := by decide

def c1593 : Contract := original1593.toContract.get (by decide)
theorem binding1593 : original1593.toContract = some c1593 := rfl

theorem checked1593 : check 4000 c1593 = true := by decide

def original1594 : RawOriginal := C012.records[58]'(by decide)
theorem original_id1594 : original1594.index = 1594 := by decide

def c1594 : Contract := original1594.toContract.get (by decide)
theorem binding1594 : original1594.toContract = some c1594 := rfl

theorem checked1594 : check 4000 c1594 = true := by decide

def original1595 : RawOriginal := C012.records[59]'(by decide)
theorem original_id1595 : original1595.index = 1595 := by decide

def c1595 : Contract := original1595.toContract.get (by decide)
theorem binding1595 : original1595.toContract = some c1595 := rfl

theorem checked1595 : check 4000 c1595 = true := by decide

def original1596 : RawOriginal := C012.records[60]'(by decide)
theorem original_id1596 : original1596.index = 1596 := by decide

def c1596 : Contract := original1596.toContract.get (by decide)
theorem binding1596 : original1596.toContract = some c1596 := rfl

theorem checked1596 : check 4000 c1596 = true := by decide

def original1597 : RawOriginal := C012.records[61]'(by decide)
theorem original_id1597 : original1597.index = 1597 := by decide

def c1597 : Contract := original1597.toContract.get (by decide)
theorem binding1597 : original1597.toContract = some c1597 := rfl

theorem checked1597 : check 4000 c1597 = true := by decide

def original1598 : RawOriginal := C012.records[62]'(by decide)
theorem original_id1598 : original1598.index = 1598 := by decide

def c1598 : Contract := original1598.toContract.get (by decide)
theorem binding1598 : original1598.toContract = some c1598 := rfl

theorem checked1598 : check 4000 c1598 = true := by decide

def original1599 : RawOriginal := C012.records[63]'(by decide)
theorem original_id1599 : original1599.index = 1599 := by decide

def c1599 : Contract := original1599.toContract.get (by decide)
theorem binding1599 : original1599.toContract = some c1599 := rfl

theorem checked1599 : check 4000 c1599 = true := by decide

def original1600 : RawOriginal := C012.records[64]'(by decide)
theorem original_id1600 : original1600.index = 1600 := by decide

def c1600 : Contract := original1600.toContract.get (by decide)
theorem binding1600 : original1600.toContract = some c1600 := rfl

theorem checked1600 : check 4000 c1600 = true := by decide

def original1601 : RawOriginal := C012.records[65]'(by decide)
theorem original_id1601 : original1601.index = 1601 := by decide

def c1601 : Contract := original1601.toContract.get (by decide)
theorem binding1601 : original1601.toContract = some c1601 := rfl

theorem checked1601 : check 4000 c1601 = true := by decide

def original1602 : RawOriginal := C012.records[66]'(by decide)
theorem original_id1602 : original1602.index = 1602 := by decide

def c1602 : Contract := original1602.toContract.get (by decide)
theorem binding1602 : original1602.toContract = some c1602 := rfl

theorem checked1602 : check 4000 c1602 = true := by decide

def original1603 : RawOriginal := C012.records[67]'(by decide)
theorem original_id1603 : original1603.index = 1603 := by decide

def c1603 : Contract := original1603.toContract.get (by decide)
theorem binding1603 : original1603.toContract = some c1603 := rfl

theorem checked1603 : check 4000 c1603 = true := by decide

def original1604 : RawOriginal := C012.records[68]'(by decide)
theorem original_id1604 : original1604.index = 1604 := by decide

def c1604 : Contract := original1604.toContract.get (by decide)
theorem binding1604 : original1604.toContract = some c1604 := rfl

theorem checked1604 : check 4000 c1604 = true := by decide

def original1605 : RawOriginal := C012.records[69]'(by decide)
theorem original_id1605 : original1605.index = 1605 := by decide

def c1605 : Contract := original1605.toContract.get (by decide)
theorem binding1605 : original1605.toContract = some c1605 := rfl

theorem checked1605 : check 4000 c1605 = true := by decide

def records : List Certified := [
  ⟨1590, c1590, 4000, checked1590⟩,
  ⟨1591, c1591, 4000, checked1591⟩,
  ⟨1592, c1592, 4000, checked1592⟩,
  ⟨1593, c1593, 4000, checked1593⟩,
  ⟨1594, c1594, 4000, checked1594⟩,
  ⟨1595, c1595, 4000, checked1595⟩,
  ⟨1596, c1596, 4000, checked1596⟩,
  ⟨1597, c1597, 4000, checked1597⟩,
  ⟨1598, c1598, 4000, checked1598⟩,
  ⟨1599, c1599, 4000, checked1599⟩,
  ⟨1600, c1600, 4000, checked1600⟩,
  ⟨1601, c1601, 4000, checked1601⟩,
  ⟨1602, c1602, 4000, checked1602⟩,
  ⟨1603, c1603, 4000, checked1603⟩,
  ⟨1604, c1604, 4000, checked1604⟩,
  ⟨1605, c1605, 4000, checked1605⟩]

end PA215.ContractShards.Shard012Part3
