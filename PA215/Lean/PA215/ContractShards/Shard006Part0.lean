import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part0
open PA215.Contracts PA215.Census

def original774 : RawOriginal := C006.records[6]'(by decide)
theorem original_id774 : original774.index = 774 := by decide

def c774 : Contract := original774.toContract.get (by decide)
theorem binding774 : original774.toContract = some c774 := rfl

theorem checked774 : check 4000 c774 = true := by decide

def original775 : RawOriginal := C006.records[7]'(by decide)
theorem original_id775 : original775.index = 775 := by decide

def c775 : Contract := original775.toContract.get (by decide)
theorem binding775 : original775.toContract = some c775 := rfl

theorem checked775 : check 4000 c775 = true := by decide

def original776 : RawOriginal := C006.records[8]'(by decide)
theorem original_id776 : original776.index = 776 := by decide

def c776 : Contract := original776.toContract.get (by decide)
theorem binding776 : original776.toContract = some c776 := rfl

theorem checked776 : check 4000 c776 = true := by decide

def original777 : RawOriginal := C006.records[9]'(by decide)
theorem original_id777 : original777.index = 777 := by decide

def c777 : Contract := original777.toContract.get (by decide)
theorem binding777 : original777.toContract = some c777 := rfl

theorem checked777 : check 4000 c777 = true := by decide

def original778 : RawOriginal := C006.records[10]'(by decide)
theorem original_id778 : original778.index = 778 := by decide

def c778 : Contract := original778.toContract.get (by decide)
theorem binding778 : original778.toContract = some c778 := rfl

theorem checked778 : check 4000 c778 = true := by decide

def original779 : RawOriginal := C006.records[11]'(by decide)
theorem original_id779 : original779.index = 779 := by decide

def c779 : Contract := original779.toContract.get (by decide)
theorem binding779 : original779.toContract = some c779 := rfl

theorem checked779 : check 4000 c779 = true := by decide

def original780 : RawOriginal := C006.records[12]'(by decide)
theorem original_id780 : original780.index = 780 := by decide

def c780 : Contract := original780.toContract.get (by decide)
theorem binding780 : original780.toContract = some c780 := rfl

theorem checked780 : check 4000 c780 = true := by decide

def original781 : RawOriginal := C006.records[13]'(by decide)
theorem original_id781 : original781.index = 781 := by decide

def c781 : Contract := original781.toContract.get (by decide)
theorem binding781 : original781.toContract = some c781 := rfl

theorem checked781 : check 4000 c781 = true := by decide

def original782 : RawOriginal := C006.records[14]'(by decide)
theorem original_id782 : original782.index = 782 := by decide

def c782 : Contract := original782.toContract.get (by decide)
theorem binding782 : original782.toContract = some c782 := rfl

theorem checked782 : check 4000 c782 = true := by decide

def original783 : RawOriginal := C006.records[15]'(by decide)
theorem original_id783 : original783.index = 783 := by decide

def c783 : Contract := original783.toContract.get (by decide)
theorem binding783 : original783.toContract = some c783 := rfl

theorem checked783 : check 4000 c783 = true := by decide

def original784 : RawOriginal := C006.records[16]'(by decide)
theorem original_id784 : original784.index = 784 := by decide

def c784 : Contract := original784.toContract.get (by decide)
theorem binding784 : original784.toContract = some c784 := rfl

theorem checked784 : check 4000 c784 = true := by decide

def original785 : RawOriginal := C006.records[17]'(by decide)
theorem original_id785 : original785.index = 785 := by decide

def c785 : Contract := original785.toContract.get (by decide)
theorem binding785 : original785.toContract = some c785 := rfl

theorem checked785 : check 4000 c785 = true := by decide

def original786 : RawOriginal := C006.records[18]'(by decide)
theorem original_id786 : original786.index = 786 := by decide

def c786 : Contract := original786.toContract.get (by decide)
theorem binding786 : original786.toContract = some c786 := rfl

theorem checked786 : check 4000 c786 = true := by decide

def original787 : RawOriginal := C006.records[19]'(by decide)
theorem original_id787 : original787.index = 787 := by decide

def c787 : Contract := original787.toContract.get (by decide)
theorem binding787 : original787.toContract = some c787 := rfl

theorem checked787 : check 4000 c787 = true := by decide

def original788 : RawOriginal := C006.records[20]'(by decide)
theorem original_id788 : original788.index = 788 := by decide

def c788 : Contract := original788.toContract.get (by decide)
theorem binding788 : original788.toContract = some c788 := rfl

theorem checked788 : check 4000 c788 = true := by decide

def original789 : RawOriginal := C006.records[21]'(by decide)
theorem original_id789 : original789.index = 789 := by decide

def c789 : Contract := original789.toContract.get (by decide)
theorem binding789 : original789.toContract = some c789 := rfl

theorem checked789 : check 4000 c789 = true := by decide

def records : List Certified := [
  ⟨774, c774, 4000, checked774⟩,
  ⟨775, c775, 4000, checked775⟩,
  ⟨776, c776, 4000, checked776⟩,
  ⟨777, c777, 4000, checked777⟩,
  ⟨778, c778, 4000, checked778⟩,
  ⟨779, c779, 4000, checked779⟩,
  ⟨780, c780, 4000, checked780⟩,
  ⟨781, c781, 4000, checked781⟩,
  ⟨782, c782, 4000, checked782⟩,
  ⟨783, c783, 4000, checked783⟩,
  ⟨784, c784, 4000, checked784⟩,
  ⟨785, c785, 4000, checked785⟩,
  ⟨786, c786, 4000, checked786⟩,
  ⟨787, c787, 4000, checked787⟩,
  ⟨788, c788, 4000, checked788⟩,
  ⟨789, c789, 4000, checked789⟩]

end PA215.ContractShards.Shard006Part0
