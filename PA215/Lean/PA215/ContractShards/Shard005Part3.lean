import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part3
open PA215.Contracts PA215.Census

def original694 : RawOriginal := C005.records[54]'(by decide)
theorem original_id694 : original694.index = 694 := by decide

def c694 : Contract := original694.toContract.get (by decide)
theorem binding694 : original694.toContract = some c694 := rfl

theorem checked694 : check 4000 c694 = true := by decide

def original695 : RawOriginal := C005.records[55]'(by decide)
theorem original_id695 : original695.index = 695 := by decide

def c695 : Contract := original695.toContract.get (by decide)
theorem binding695 : original695.toContract = some c695 := rfl

theorem checked695 : check 4000 c695 = true := by decide

def original696 : RawOriginal := C005.records[56]'(by decide)
theorem original_id696 : original696.index = 696 := by decide

def c696 : Contract := original696.toContract.get (by decide)
theorem binding696 : original696.toContract = some c696 := rfl

theorem checked696 : check 4000 c696 = true := by decide

def original697 : RawOriginal := C005.records[57]'(by decide)
theorem original_id697 : original697.index = 697 := by decide

def c697 : Contract := original697.toContract.get (by decide)
theorem binding697 : original697.toContract = some c697 := rfl

theorem checked697 : check 4000 c697 = true := by decide

def original698 : RawOriginal := C005.records[58]'(by decide)
theorem original_id698 : original698.index = 698 := by decide

def c698 : Contract := original698.toContract.get (by decide)
theorem binding698 : original698.toContract = some c698 := rfl

theorem checked698 : check 4000 c698 = true := by decide

def original699 : RawOriginal := C005.records[59]'(by decide)
theorem original_id699 : original699.index = 699 := by decide

def c699 : Contract := original699.toContract.get (by decide)
theorem binding699 : original699.toContract = some c699 := rfl

theorem checked699 : check 4000 c699 = true := by decide

def original700 : RawOriginal := C005.records[60]'(by decide)
theorem original_id700 : original700.index = 700 := by decide

def c700 : Contract := original700.toContract.get (by decide)
theorem binding700 : original700.toContract = some c700 := rfl

theorem checked700 : check 4000 c700 = true := by decide

def original701 : RawOriginal := C005.records[61]'(by decide)
theorem original_id701 : original701.index = 701 := by decide

def c701 : Contract := original701.toContract.get (by decide)
theorem binding701 : original701.toContract = some c701 := rfl

theorem checked701 : check 4000 c701 = true := by decide

def original702 : RawOriginal := C005.records[62]'(by decide)
theorem original_id702 : original702.index = 702 := by decide

def c702 : Contract := original702.toContract.get (by decide)
theorem binding702 : original702.toContract = some c702 := rfl

theorem checked702 : check 4000 c702 = true := by decide

def original703 : RawOriginal := C005.records[63]'(by decide)
theorem original_id703 : original703.index = 703 := by decide

def c703 : Contract := original703.toContract.get (by decide)
theorem binding703 : original703.toContract = some c703 := rfl

theorem checked703 : check 4000 c703 = true := by decide

def original704 : RawOriginal := C005.records[64]'(by decide)
theorem original_id704 : original704.index = 704 := by decide

def c704 : Contract := original704.toContract.get (by decide)
theorem binding704 : original704.toContract = some c704 := rfl

theorem checked704 : check 4000 c704 = true := by decide

def original705 : RawOriginal := C005.records[65]'(by decide)
theorem original_id705 : original705.index = 705 := by decide

def c705 : Contract := original705.toContract.get (by decide)
theorem binding705 : original705.toContract = some c705 := rfl

theorem checked705 : check 4000 c705 = true := by decide

def original706 : RawOriginal := C005.records[66]'(by decide)
theorem original_id706 : original706.index = 706 := by decide

def c706 : Contract := original706.toContract.get (by decide)
theorem binding706 : original706.toContract = some c706 := rfl

theorem checked706 : check 4000 c706 = true := by decide

def original707 : RawOriginal := C005.records[67]'(by decide)
theorem original_id707 : original707.index = 707 := by decide

def c707 : Contract := original707.toContract.get (by decide)
theorem binding707 : original707.toContract = some c707 := rfl

theorem checked707 : check 4000 c707 = true := by decide

def original708 : RawOriginal := C005.records[68]'(by decide)
theorem original_id708 : original708.index = 708 := by decide

def c708 : Contract := original708.toContract.get (by decide)
theorem binding708 : original708.toContract = some c708 := rfl

theorem checked708 : check 4000 c708 = true := by decide

def original709 : RawOriginal := C005.records[69]'(by decide)
theorem original_id709 : original709.index = 709 := by decide

def c709 : Contract := original709.toContract.get (by decide)
theorem binding709 : original709.toContract = some c709 := rfl

theorem checked709 : check 4000 c709 = true := by decide

def records : List Certified := [
  ⟨694, c694, 4000, checked694⟩,
  ⟨695, c695, 4000, checked695⟩,
  ⟨696, c696, 4000, checked696⟩,
  ⟨697, c697, 4000, checked697⟩,
  ⟨698, c698, 4000, checked698⟩,
  ⟨699, c699, 4000, checked699⟩,
  ⟨700, c700, 4000, checked700⟩,
  ⟨701, c701, 4000, checked701⟩,
  ⟨702, c702, 4000, checked702⟩,
  ⟨703, c703, 4000, checked703⟩,
  ⟨704, c704, 4000, checked704⟩,
  ⟨705, c705, 4000, checked705⟩,
  ⟨706, c706, 4000, checked706⟩,
  ⟨707, c707, 4000, checked707⟩,
  ⟨708, c708, 4000, checked708⟩,
  ⟨709, c709, 4000, checked709⟩]

end PA215.ContractShards.Shard005Part3
