import PA215.CertifiedContracts
import PA215.Census.C005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005Part2
open PA215.Contracts PA215.Census

def original678 : RawOriginal := C005.records[38]'(by decide)
theorem original_id678 : original678.index = 678 := by decide

def c678 : Contract := original678.toContract.get (by decide)
theorem binding678 : original678.toContract = some c678 := rfl

theorem checked678 : check 4000 c678 = true := by decide

def original679 : RawOriginal := C005.records[39]'(by decide)
theorem original_id679 : original679.index = 679 := by decide

def c679 : Contract := original679.toContract.get (by decide)
theorem binding679 : original679.toContract = some c679 := rfl

theorem checked679 : check 4000 c679 = true := by decide

def original680 : RawOriginal := C005.records[40]'(by decide)
theorem original_id680 : original680.index = 680 := by decide

def c680 : Contract := original680.toContract.get (by decide)
theorem binding680 : original680.toContract = some c680 := rfl

theorem checked680 : check 4000 c680 = true := by decide

def original681 : RawOriginal := C005.records[41]'(by decide)
theorem original_id681 : original681.index = 681 := by decide

def c681 : Contract := original681.toContract.get (by decide)
theorem binding681 : original681.toContract = some c681 := rfl

theorem checked681 : check 4000 c681 = true := by decide

def original682 : RawOriginal := C005.records[42]'(by decide)
theorem original_id682 : original682.index = 682 := by decide

def c682 : Contract := original682.toContract.get (by decide)
theorem binding682 : original682.toContract = some c682 := rfl

theorem checked682 : check 4000 c682 = true := by decide

def original683 : RawOriginal := C005.records[43]'(by decide)
theorem original_id683 : original683.index = 683 := by decide

def c683 : Contract := original683.toContract.get (by decide)
theorem binding683 : original683.toContract = some c683 := rfl

theorem checked683 : check 4000 c683 = true := by decide

def original684 : RawOriginal := C005.records[44]'(by decide)
theorem original_id684 : original684.index = 684 := by decide

def c684 : Contract := original684.toContract.get (by decide)
theorem binding684 : original684.toContract = some c684 := rfl

theorem checked684 : check 4000 c684 = true := by decide

def original685 : RawOriginal := C005.records[45]'(by decide)
theorem original_id685 : original685.index = 685 := by decide

def c685 : Contract := original685.toContract.get (by decide)
theorem binding685 : original685.toContract = some c685 := rfl

theorem checked685 : check 4000 c685 = true := by decide

def original686 : RawOriginal := C005.records[46]'(by decide)
theorem original_id686 : original686.index = 686 := by decide

def c686 : Contract := original686.toContract.get (by decide)
theorem binding686 : original686.toContract = some c686 := rfl

theorem checked686 : check 4000 c686 = true := by decide

def original687 : RawOriginal := C005.records[47]'(by decide)
theorem original_id687 : original687.index = 687 := by decide

def c687 : Contract := original687.toContract.get (by decide)
theorem binding687 : original687.toContract = some c687 := rfl

theorem checked687 : check 4000 c687 = true := by decide

def original688 : RawOriginal := C005.records[48]'(by decide)
theorem original_id688 : original688.index = 688 := by decide

def c688 : Contract := original688.toContract.get (by decide)
theorem binding688 : original688.toContract = some c688 := rfl

theorem checked688 : check 4000 c688 = true := by decide

def original689 : RawOriginal := C005.records[49]'(by decide)
theorem original_id689 : original689.index = 689 := by decide

def c689 : Contract := original689.toContract.get (by decide)
theorem binding689 : original689.toContract = some c689 := rfl

theorem checked689 : check 4000 c689 = true := by decide

def original690 : RawOriginal := C005.records[50]'(by decide)
theorem original_id690 : original690.index = 690 := by decide

def c690 : Contract := original690.toContract.get (by decide)
theorem binding690 : original690.toContract = some c690 := rfl

theorem checked690 : check 4000 c690 = true := by decide

def original691 : RawOriginal := C005.records[51]'(by decide)
theorem original_id691 : original691.index = 691 := by decide

def c691 : Contract := original691.toContract.get (by decide)
theorem binding691 : original691.toContract = some c691 := rfl

theorem checked691 : check 4000 c691 = true := by decide

def original692 : RawOriginal := C005.records[52]'(by decide)
theorem original_id692 : original692.index = 692 := by decide

def c692 : Contract := original692.toContract.get (by decide)
theorem binding692 : original692.toContract = some c692 := rfl

theorem checked692 : check 4000 c692 = true := by decide

def original693 : RawOriginal := C005.records[53]'(by decide)
theorem original_id693 : original693.index = 693 := by decide

def c693 : Contract := original693.toContract.get (by decide)
theorem binding693 : original693.toContract = some c693 := rfl

theorem checked693 : check 4000 c693 = true := by decide

def records : List Certified := [
  ⟨678, c678, 4000, checked678⟩,
  ⟨679, c679, 4000, checked679⟩,
  ⟨680, c680, 4000, checked680⟩,
  ⟨681, c681, 4000, checked681⟩,
  ⟨682, c682, 4000, checked682⟩,
  ⟨683, c683, 4000, checked683⟩,
  ⟨684, c684, 4000, checked684⟩,
  ⟨685, c685, 4000, checked685⟩,
  ⟨686, c686, 4000, checked686⟩,
  ⟨687, c687, 4000, checked687⟩,
  ⟨688, c688, 4000, checked688⟩,
  ⟨689, c689, 4000, checked689⟩,
  ⟨690, c690, 4000, checked690⟩,
  ⟨691, c691, 4000, checked691⟩,
  ⟨692, c692, 4000, checked692⟩,
  ⟨693, c693, 4000, checked693⟩]

end PA215.ContractShards.Shard005Part2
