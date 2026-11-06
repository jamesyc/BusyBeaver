import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part4
open PA215.Contracts PA215.Census

def original838 : RawOriginal := C006.records[70]'(by decide)
theorem original_id838 : original838.index = 838 := by decide

def c838 : Contract := original838.toContract.get (by decide)
theorem binding838 : original838.toContract = some c838 := rfl

theorem checked838 : check 4000 c838 = true := by decide

def original839 : RawOriginal := C006.records[71]'(by decide)
theorem original_id839 : original839.index = 839 := by decide

def c839 : Contract := original839.toContract.get (by decide)
theorem binding839 : original839.toContract = some c839 := rfl

theorem checked839 : check 4000 c839 = true := by decide

def original840 : RawOriginal := C006.records[72]'(by decide)
theorem original_id840 : original840.index = 840 := by decide

def c840 : Contract := original840.toContract.get (by decide)
theorem binding840 : original840.toContract = some c840 := rfl

theorem checked840 : check 4000 c840 = true := by decide

def original841 : RawOriginal := C006.records[73]'(by decide)
theorem original_id841 : original841.index = 841 := by decide

def c841 : Contract := original841.toContract.get (by decide)
theorem binding841 : original841.toContract = some c841 := rfl

theorem checked841 : check 4000 c841 = true := by decide

def original842 : RawOriginal := C006.records[74]'(by decide)
theorem original_id842 : original842.index = 842 := by decide

def c842 : Contract := original842.toContract.get (by decide)
theorem binding842 : original842.toContract = some c842 := rfl

theorem checked842 : check 4000 c842 = true := by decide

def original843 : RawOriginal := C006.records[75]'(by decide)
theorem original_id843 : original843.index = 843 := by decide

def c843 : Contract := original843.toContract.get (by decide)
theorem binding843 : original843.toContract = some c843 := rfl

theorem checked843 : check 4000 c843 = true := by decide

def original844 : RawOriginal := C006.records[76]'(by decide)
theorem original_id844 : original844.index = 844 := by decide

def c844 : Contract := original844.toContract.get (by decide)
theorem binding844 : original844.toContract = some c844 := rfl

theorem checked844 : check 4000 c844 = true := by decide

def original845 : RawOriginal := C006.records[77]'(by decide)
theorem original_id845 : original845.index = 845 := by decide

def c845 : Contract := original845.toContract.get (by decide)
theorem binding845 : original845.toContract = some c845 := rfl

theorem checked845 : check 4000 c845 = true := by decide

def original846 : RawOriginal := C006.records[78]'(by decide)
theorem original_id846 : original846.index = 846 := by decide

def c846 : Contract := original846.toContract.get (by decide)
theorem binding846 : original846.toContract = some c846 := rfl

theorem checked846 : check 4000 c846 = true := by decide

def original847 : RawOriginal := C006.records[79]'(by decide)
theorem original_id847 : original847.index = 847 := by decide

def c847 : Contract := original847.toContract.get (by decide)
theorem binding847 : original847.toContract = some c847 := rfl

theorem checked847 : check 4000 c847 = true := by decide

def original848 : RawOriginal := C006.records[80]'(by decide)
theorem original_id848 : original848.index = 848 := by decide

def c848 : Contract := original848.toContract.get (by decide)
theorem binding848 : original848.toContract = some c848 := rfl

theorem checked848 : check 4000 c848 = true := by decide

def original849 : RawOriginal := C006.records[81]'(by decide)
theorem original_id849 : original849.index = 849 := by decide

def c849 : Contract := original849.toContract.get (by decide)
theorem binding849 : original849.toContract = some c849 := rfl

theorem checked849 : check 4000 c849 = true := by decide

def original850 : RawOriginal := C006.records[82]'(by decide)
theorem original_id850 : original850.index = 850 := by decide

def c850 : Contract := original850.toContract.get (by decide)
theorem binding850 : original850.toContract = some c850 := rfl

theorem checked850 : check 4000 c850 = true := by decide

def original851 : RawOriginal := C006.records[83]'(by decide)
theorem original_id851 : original851.index = 851 := by decide

def c851 : Contract := original851.toContract.get (by decide)
theorem binding851 : original851.toContract = some c851 := rfl

theorem checked851 : check 4000 c851 = true := by decide

def original852 : RawOriginal := C006.records[84]'(by decide)
theorem original_id852 : original852.index = 852 := by decide

def c852 : Contract := original852.toContract.get (by decide)
theorem binding852 : original852.toContract = some c852 := rfl

theorem checked852 : check 4000 c852 = true := by decide

def original853 : RawOriginal := C006.records[85]'(by decide)
theorem original_id853 : original853.index = 853 := by decide

def c853 : Contract := original853.toContract.get (by decide)
theorem binding853 : original853.toContract = some c853 := rfl

theorem checked853 : check 4000 c853 = true := by decide

def records : List Certified := [
  ⟨838, c838, 4000, checked838⟩,
  ⟨839, c839, 4000, checked839⟩,
  ⟨840, c840, 4000, checked840⟩,
  ⟨841, c841, 4000, checked841⟩,
  ⟨842, c842, 4000, checked842⟩,
  ⟨843, c843, 4000, checked843⟩,
  ⟨844, c844, 4000, checked844⟩,
  ⟨845, c845, 4000, checked845⟩,
  ⟨846, c846, 4000, checked846⟩,
  ⟨847, c847, 4000, checked847⟩,
  ⟨848, c848, 4000, checked848⟩,
  ⟨849, c849, 4000, checked849⟩,
  ⟨850, c850, 4000, checked850⟩,
  ⟨851, c851, 4000, checked851⟩,
  ⟨852, c852, 4000, checked852⟩,
  ⟨853, c853, 4000, checked853⟩]

end PA215.ContractShards.Shard006Part4
