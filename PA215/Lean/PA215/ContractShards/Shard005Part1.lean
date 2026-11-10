import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part1
open PA215.Contracts PA215.Census

def original662 : RawOriginal := C005.records[22]'(by decide)
theorem original_id662 : original662.index = 662 := by decide

def c662 : Contract := original662.toContract.get (by decide)
theorem binding662 : original662.toContract = some c662 := rfl

theorem checked662 : check 4000 c662 = true := by decide

def original663 : RawOriginal := C005.records[23]'(by decide)
theorem original_id663 : original663.index = 663 := by decide

def c663 : Contract := original663.toContract.get (by decide)
theorem binding663 : original663.toContract = some c663 := rfl

theorem checked663 : check 4000 c663 = true := by decide

def original664 : RawOriginal := C005.records[24]'(by decide)
theorem original_id664 : original664.index = 664 := by decide

def c664 : Contract := original664.toContract.get (by decide)
theorem binding664 : original664.toContract = some c664 := rfl

theorem checked664 : check 4000 c664 = true := by decide

def original665 : RawOriginal := C005.records[25]'(by decide)
theorem original_id665 : original665.index = 665 := by decide

def c665 : Contract := original665.toContract.get (by decide)
theorem binding665 : original665.toContract = some c665 := rfl

theorem checked665 : check 4000 c665 = true := by decide

def original666 : RawOriginal := C005.records[26]'(by decide)
theorem original_id666 : original666.index = 666 := by decide

def c666 : Contract := original666.toContract.get (by decide)
theorem binding666 : original666.toContract = some c666 := rfl

theorem checked666 : check 4000 c666 = true := by decide

def original667 : RawOriginal := C005.records[27]'(by decide)
theorem original_id667 : original667.index = 667 := by decide

def c667 : Contract := original667.toContract.get (by decide)
theorem binding667 : original667.toContract = some c667 := rfl

theorem checked667 : check 4000 c667 = true := by decide

def original668 : RawOriginal := C005.records[28]'(by decide)
theorem original_id668 : original668.index = 668 := by decide

def c668 : Contract := original668.toContract.get (by decide)
theorem binding668 : original668.toContract = some c668 := rfl

theorem checked668 : check 4000 c668 = true := by decide

def original669 : RawOriginal := C005.records[29]'(by decide)
theorem original_id669 : original669.index = 669 := by decide

def c669 : Contract := original669.toContract.get (by decide)
theorem binding669 : original669.toContract = some c669 := rfl

theorem checked669 : check 4000 c669 = true := by decide

def original670 : RawOriginal := C005.records[30]'(by decide)
theorem original_id670 : original670.index = 670 := by decide

def c670 : Contract := original670.toContract.get (by decide)
theorem binding670 : original670.toContract = some c670 := rfl

theorem checked670 : check 4000 c670 = true := by decide

def original671 : RawOriginal := C005.records[31]'(by decide)
theorem original_id671 : original671.index = 671 := by decide

def c671 : Contract := original671.toContract.get (by decide)
theorem binding671 : original671.toContract = some c671 := rfl

theorem checked671 : check 4000 c671 = true := by decide

def original672 : RawOriginal := C005.records[32]'(by decide)
theorem original_id672 : original672.index = 672 := by decide

def c672 : Contract := original672.toContract.get (by decide)
theorem binding672 : original672.toContract = some c672 := rfl

theorem checked672 : check 4000 c672 = true := by decide

def original673 : RawOriginal := C005.records[33]'(by decide)
theorem original_id673 : original673.index = 673 := by decide

def c673 : Contract := original673.toContract.get (by decide)
theorem binding673 : original673.toContract = some c673 := rfl

theorem checked673 : check 4000 c673 = true := by decide

def original674 : RawOriginal := C005.records[34]'(by decide)
theorem original_id674 : original674.index = 674 := by decide

def c674 : Contract := original674.toContract.get (by decide)
theorem binding674 : original674.toContract = some c674 := rfl

theorem checked674 : check 4000 c674 = true := by decide

def original675 : RawOriginal := C005.records[35]'(by decide)
theorem original_id675 : original675.index = 675 := by decide

def c675 : Contract := original675.toContract.get (by decide)
theorem binding675 : original675.toContract = some c675 := rfl

theorem checked675 : check 4000 c675 = true := by decide

def original676 : RawOriginal := C005.records[36]'(by decide)
theorem original_id676 : original676.index = 676 := by decide

def c676 : Contract := original676.toContract.get (by decide)
theorem binding676 : original676.toContract = some c676 := rfl

theorem checked676 : check 4000 c676 = true := by decide

def original677 : RawOriginal := C005.records[37]'(by decide)
theorem original_id677 : original677.index = 677 := by decide

def c677 : Contract := original677.toContract.get (by decide)
theorem binding677 : original677.toContract = some c677 := rfl

theorem checked677 : check 4000 c677 = true := by decide

def records : List Certified := [
  ⟨662, c662, 4000, checked662⟩,
  ⟨663, c663, 4000, checked663⟩,
  ⟨664, c664, 4000, checked664⟩,
  ⟨665, c665, 4000, checked665⟩,
  ⟨666, c666, 4000, checked666⟩,
  ⟨667, c667, 4000, checked667⟩,
  ⟨668, c668, 4000, checked668⟩,
  ⟨669, c669, 4000, checked669⟩,
  ⟨670, c670, 4000, checked670⟩,
  ⟨671, c671, 4000, checked671⟩,
  ⟨672, c672, 4000, checked672⟩,
  ⟨673, c673, 4000, checked673⟩,
  ⟨674, c674, 4000, checked674⟩,
  ⟨675, c675, 4000, checked675⟩,
  ⟨676, c676, 4000, checked676⟩,
  ⟨677, c677, 4000, checked677⟩]

end PA215.ContractShards.Shard005Part1
