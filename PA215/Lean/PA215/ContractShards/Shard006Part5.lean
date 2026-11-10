import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part5
open PA215.Contracts PA215.Census

def original854 : RawOriginal := C006.records[86]'(by decide)
theorem original_id854 : original854.index = 854 := by decide

def c854 : Contract := original854.toContract.get (by decide)
theorem binding854 : original854.toContract = some c854 := rfl

theorem checked854 : check 4000 c854 = true := by decide

def original855 : RawOriginal := C006.records[87]'(by decide)
theorem original_id855 : original855.index = 855 := by decide

def c855 : Contract := original855.toContract.get (by decide)
theorem binding855 : original855.toContract = some c855 := rfl

theorem checked855 : check 4000 c855 = true := by decide

def original856 : RawOriginal := C006.records[88]'(by decide)
theorem original_id856 : original856.index = 856 := by decide

def c856 : Contract := original856.toContract.get (by decide)
theorem binding856 : original856.toContract = some c856 := rfl

theorem checked856 : check 4000 c856 = true := by decide

def original857 : RawOriginal := C006.records[89]'(by decide)
theorem original_id857 : original857.index = 857 := by decide

def c857 : Contract := original857.toContract.get (by decide)
theorem binding857 : original857.toContract = some c857 := rfl

theorem checked857 : check 4000 c857 = true := by decide

def original858 : RawOriginal := C006.records[90]'(by decide)
theorem original_id858 : original858.index = 858 := by decide

def c858 : Contract := original858.toContract.get (by decide)
theorem binding858 : original858.toContract = some c858 := rfl

theorem checked858 : check 4000 c858 = true := by decide

def original859 : RawOriginal := C006.records[91]'(by decide)
theorem original_id859 : original859.index = 859 := by decide

def c859 : Contract := original859.toContract.get (by decide)
theorem binding859 : original859.toContract = some c859 := rfl

theorem checked859 : check 4000 c859 = true := by decide

def original860 : RawOriginal := C006.records[92]'(by decide)
theorem original_id860 : original860.index = 860 := by decide

def c860 : Contract := original860.toContract.get (by decide)
theorem binding860 : original860.toContract = some c860 := rfl

theorem checked860 : check 4000 c860 = true := by decide

def original861 : RawOriginal := C006.records[93]'(by decide)
theorem original_id861 : original861.index = 861 := by decide

def c861 : Contract := original861.toContract.get (by decide)
theorem binding861 : original861.toContract = some c861 := rfl

theorem checked861 : check 4000 c861 = true := by decide

def original862 : RawOriginal := C006.records[94]'(by decide)
theorem original_id862 : original862.index = 862 := by decide

def c862 : Contract := original862.toContract.get (by decide)
theorem binding862 : original862.toContract = some c862 := rfl

theorem checked862 : check 4000 c862 = true := by decide

def original863 : RawOriginal := C006.records[95]'(by decide)
theorem original_id863 : original863.index = 863 := by decide

def c863 : Contract := original863.toContract.get (by decide)
theorem binding863 : original863.toContract = some c863 := rfl

theorem checked863 : check 4000 c863 = true := by decide

def original864 : RawOriginal := C006.records[96]'(by decide)
theorem original_id864 : original864.index = 864 := by decide

def c864 : Contract := original864.toContract.get (by decide)
theorem binding864 : original864.toContract = some c864 := rfl

theorem checked864 : check 4000 c864 = true := by decide

def original865 : RawOriginal := C006.records[97]'(by decide)
theorem original_id865 : original865.index = 865 := by decide

def c865 : Contract := original865.toContract.get (by decide)
theorem binding865 : original865.toContract = some c865 := rfl

theorem checked865 : check 4000 c865 = true := by decide

def original866 : RawOriginal := C006.records[98]'(by decide)
theorem original_id866 : original866.index = 866 := by decide

def c866 : Contract := original866.toContract.get (by decide)
theorem binding866 : original866.toContract = some c866 := rfl

theorem checked866 : check 4000 c866 = true := by decide

def original867 : RawOriginal := C006.records[99]'(by decide)
theorem original_id867 : original867.index = 867 := by decide

def c867 : Contract := original867.toContract.get (by decide)
theorem binding867 : original867.toContract = some c867 := rfl

theorem checked867 : check 4000 c867 = true := by decide

def original868 : RawOriginal := C006.records[100]'(by decide)
theorem original_id868 : original868.index = 868 := by decide

def c868 : Contract := original868.toContract.get (by decide)
theorem binding868 : original868.toContract = some c868 := rfl

theorem checked868 : check 4000 c868 = true := by decide

def original869 : RawOriginal := C006.records[101]'(by decide)
theorem original_id869 : original869.index = 869 := by decide

def c869 : Contract := original869.toContract.get (by decide)
theorem binding869 : original869.toContract = some c869 := rfl

theorem checked869 : check 4000 c869 = true := by decide

def records : List Certified := [
  ⟨854, c854, 4000, checked854⟩,
  ⟨855, c855, 4000, checked855⟩,
  ⟨856, c856, 4000, checked856⟩,
  ⟨857, c857, 4000, checked857⟩,
  ⟨858, c858, 4000, checked858⟩,
  ⟨859, c859, 4000, checked859⟩,
  ⟨860, c860, 4000, checked860⟩,
  ⟨861, c861, 4000, checked861⟩,
  ⟨862, c862, 4000, checked862⟩,
  ⟨863, c863, 4000, checked863⟩,
  ⟨864, c864, 4000, checked864⟩,
  ⟨865, c865, 4000, checked865⟩,
  ⟨866, c866, 4000, checked866⟩,
  ⟨867, c867, 4000, checked867⟩,
  ⟨868, c868, 4000, checked868⟩,
  ⟨869, c869, 4000, checked869⟩]

end PA215.ContractShards.Shard006Part5
