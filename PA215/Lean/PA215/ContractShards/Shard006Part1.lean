import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part1
open PA215.Contracts PA215.Census

def original790 : RawOriginal := C006.records[22]'(by decide)
theorem original_id790 : original790.index = 790 := by decide

def c790 : Contract := original790.toContract.get (by decide)
theorem binding790 : original790.toContract = some c790 := rfl

theorem checked790 : check 4000 c790 = true := by decide

def original791 : RawOriginal := C006.records[23]'(by decide)
theorem original_id791 : original791.index = 791 := by decide

def c791 : Contract := original791.toContract.get (by decide)
theorem binding791 : original791.toContract = some c791 := rfl

theorem checked791 : check 4000 c791 = true := by decide

def original792 : RawOriginal := C006.records[24]'(by decide)
theorem original_id792 : original792.index = 792 := by decide

def c792 : Contract := original792.toContract.get (by decide)
theorem binding792 : original792.toContract = some c792 := rfl

theorem checked792 : check 4000 c792 = true := by decide

def original793 : RawOriginal := C006.records[25]'(by decide)
theorem original_id793 : original793.index = 793 := by decide

def c793 : Contract := original793.toContract.get (by decide)
theorem binding793 : original793.toContract = some c793 := rfl

theorem checked793 : check 4000 c793 = true := by decide

def original794 : RawOriginal := C006.records[26]'(by decide)
theorem original_id794 : original794.index = 794 := by decide

def c794 : Contract := original794.toContract.get (by decide)
theorem binding794 : original794.toContract = some c794 := rfl

theorem checked794 : check 4000 c794 = true := by decide

def original795 : RawOriginal := C006.records[27]'(by decide)
theorem original_id795 : original795.index = 795 := by decide

def c795 : Contract := original795.toContract.get (by decide)
theorem binding795 : original795.toContract = some c795 := rfl

theorem checked795 : check 4000 c795 = true := by decide

def original796 : RawOriginal := C006.records[28]'(by decide)
theorem original_id796 : original796.index = 796 := by decide

def c796 : Contract := original796.toContract.get (by decide)
theorem binding796 : original796.toContract = some c796 := rfl

theorem checked796 : check 4000 c796 = true := by decide

def original797 : RawOriginal := C006.records[29]'(by decide)
theorem original_id797 : original797.index = 797 := by decide

def c797 : Contract := original797.toContract.get (by decide)
theorem binding797 : original797.toContract = some c797 := rfl

theorem checked797 : check 4000 c797 = true := by decide

def original798 : RawOriginal := C006.records[30]'(by decide)
theorem original_id798 : original798.index = 798 := by decide

def c798 : Contract := original798.toContract.get (by decide)
theorem binding798 : original798.toContract = some c798 := rfl

theorem checked798 : check 4000 c798 = true := by decide

def original799 : RawOriginal := C006.records[31]'(by decide)
theorem original_id799 : original799.index = 799 := by decide

def c799 : Contract := original799.toContract.get (by decide)
theorem binding799 : original799.toContract = some c799 := rfl

theorem checked799 : check 4000 c799 = true := by decide

def original800 : RawOriginal := C006.records[32]'(by decide)
theorem original_id800 : original800.index = 800 := by decide

def c800 : Contract := original800.toContract.get (by decide)
theorem binding800 : original800.toContract = some c800 := rfl

theorem checked800 : check 4000 c800 = true := by decide

def original801 : RawOriginal := C006.records[33]'(by decide)
theorem original_id801 : original801.index = 801 := by decide

def c801 : Contract := original801.toContract.get (by decide)
theorem binding801 : original801.toContract = some c801 := rfl

theorem checked801 : check 4000 c801 = true := by decide

def original802 : RawOriginal := C006.records[34]'(by decide)
theorem original_id802 : original802.index = 802 := by decide

def c802 : Contract := original802.toContract.get (by decide)
theorem binding802 : original802.toContract = some c802 := rfl

theorem checked802 : check 4000 c802 = true := by decide

def original803 : RawOriginal := C006.records[35]'(by decide)
theorem original_id803 : original803.index = 803 := by decide

def c803 : Contract := original803.toContract.get (by decide)
theorem binding803 : original803.toContract = some c803 := rfl

theorem checked803 : check 4000 c803 = true := by decide

def original804 : RawOriginal := C006.records[36]'(by decide)
theorem original_id804 : original804.index = 804 := by decide

def c804 : Contract := original804.toContract.get (by decide)
theorem binding804 : original804.toContract = some c804 := rfl

theorem checked804 : check 4000 c804 = true := by decide

def original805 : RawOriginal := C006.records[37]'(by decide)
theorem original_id805 : original805.index = 805 := by decide

def c805 : Contract := original805.toContract.get (by decide)
theorem binding805 : original805.toContract = some c805 := rfl

theorem checked805 : check 4000 c805 = true := by decide

def records : List Certified := [
  ⟨790, c790, 4000, checked790⟩,
  ⟨791, c791, 4000, checked791⟩,
  ⟨792, c792, 4000, checked792⟩,
  ⟨793, c793, 4000, checked793⟩,
  ⟨794, c794, 4000, checked794⟩,
  ⟨795, c795, 4000, checked795⟩,
  ⟨796, c796, 4000, checked796⟩,
  ⟨797, c797, 4000, checked797⟩,
  ⟨798, c798, 4000, checked798⟩,
  ⟨799, c799, 4000, checked799⟩,
  ⟨800, c800, 4000, checked800⟩,
  ⟨801, c801, 4000, checked801⟩,
  ⟨802, c802, 4000, checked802⟩,
  ⟨803, c803, 4000, checked803⟩,
  ⟨804, c804, 4000, checked804⟩,
  ⟨805, c805, 4000, checked805⟩]

end PA215.ContractShards.Shard006Part1
