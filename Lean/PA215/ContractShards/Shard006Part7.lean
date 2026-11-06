import PA215.CertifiedContracts
import PA215.Census.C006
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part7
open PA215.Contracts PA215.Census

def original886 : RawOriginal := C006.records[118]'(by decide)
theorem original_id886 : original886.index = 886 := by decide

def c886 : Contract := original886.toContract.get (by decide)
theorem binding886 : original886.toContract = some c886 := rfl

theorem checked886 : check 4000 c886 = true := by decide

def original887 : RawOriginal := C006.records[119]'(by decide)
theorem original_id887 : original887.index = 887 := by decide

def c887 : Contract := original887.toContract.get (by decide)
theorem binding887 : original887.toContract = some c887 := rfl

theorem checked887 : check 4000 c887 = true := by decide

def original888 : RawOriginal := C006.records[120]'(by decide)
theorem original_id888 : original888.index = 888 := by decide

def c888 : Contract := original888.toContract.get (by decide)
theorem binding888 : original888.toContract = some c888 := rfl

theorem checked888 : check 4000 c888 = true := by decide

def original889 : RawOriginal := C006.records[121]'(by decide)
theorem original_id889 : original889.index = 889 := by decide

def c889 : Contract := original889.toContract.get (by decide)
theorem binding889 : original889.toContract = some c889 := rfl

theorem checked889 : check 4000 c889 = true := by decide

def original890 : RawOriginal := C006.records[122]'(by decide)
theorem original_id890 : original890.index = 890 := by decide

def c890 : Contract := original890.toContract.get (by decide)
theorem binding890 : original890.toContract = some c890 := rfl

theorem checked890 : check 4000 c890 = true := by decide

def original891 : RawOriginal := C006.records[123]'(by decide)
theorem original_id891 : original891.index = 891 := by decide

def c891 : Contract := original891.toContract.get (by decide)
theorem binding891 : original891.toContract = some c891 := rfl

theorem checked891 : check 4000 c891 = true := by decide

def original892 : RawOriginal := C006.records[124]'(by decide)
theorem original_id892 : original892.index = 892 := by decide

def c892 : Contract := original892.toContract.get (by decide)
theorem binding892 : original892.toContract = some c892 := rfl

theorem checked892 : check 4000 c892 = true := by decide

def original893 : RawOriginal := C006.records[125]'(by decide)
theorem original_id893 : original893.index = 893 := by decide

def c893 : Contract := original893.toContract.get (by decide)
theorem binding893 : original893.toContract = some c893 := rfl

theorem checked893 : check 4000 c893 = true := by decide

def original894 : RawOriginal := C006.records[126]'(by decide)
theorem original_id894 : original894.index = 894 := by decide

def c894 : Contract := original894.toContract.get (by decide)
theorem binding894 : original894.toContract = some c894 := rfl

theorem checked894 : check 4000 c894 = true := by decide

def original895 : RawOriginal := C006.records[127]'(by decide)
theorem original_id895 : original895.index = 895 := by decide

def c895 : Contract := original895.toContract.get (by decide)
theorem binding895 : original895.toContract = some c895 := rfl

theorem checked895 : check 4000 c895 = true := by decide

def original896 : RawOriginal := C007.records[0]'(by decide)
theorem original_id896 : original896.index = 896 := by decide

def c896 : Contract := original896.toContract.get (by decide)
theorem binding896 : original896.toContract = some c896 := rfl

theorem checked896 : check 4000 c896 = true := by decide

def original897 : RawOriginal := C007.records[1]'(by decide)
theorem original_id897 : original897.index = 897 := by decide

def c897 : Contract := original897.toContract.get (by decide)
theorem binding897 : original897.toContract = some c897 := rfl

theorem checked897 : check 4000 c897 = true := by decide

def original898 : RawOriginal := C007.records[2]'(by decide)
theorem original_id898 : original898.index = 898 := by decide

def c898 : Contract := original898.toContract.get (by decide)
theorem binding898 : original898.toContract = some c898 := rfl

theorem checked898 : check 4000 c898 = true := by decide

def original899 : RawOriginal := C007.records[3]'(by decide)
theorem original_id899 : original899.index = 899 := by decide

def c899 : Contract := original899.toContract.get (by decide)
theorem binding899 : original899.toContract = some c899 := rfl

theorem checked899 : check 4000 c899 = true := by decide

def original900 : RawOriginal := C007.records[4]'(by decide)
theorem original_id900 : original900.index = 900 := by decide

def c900 : Contract := original900.toContract.get (by decide)
theorem binding900 : original900.toContract = some c900 := rfl

theorem checked900 : check 4000 c900 = true := by decide

def original901 : RawOriginal := C007.records[5]'(by decide)
theorem original_id901 : original901.index = 901 := by decide

def c901 : Contract := original901.toContract.get (by decide)
theorem binding901 : original901.toContract = some c901 := rfl

theorem checked901 : check 4000 c901 = true := by decide

def records : List Certified := [
  ⟨886, c886, 4000, checked886⟩,
  ⟨887, c887, 4000, checked887⟩,
  ⟨888, c888, 4000, checked888⟩,
  ⟨889, c889, 4000, checked889⟩,
  ⟨890, c890, 4000, checked890⟩,
  ⟨891, c891, 4000, checked891⟩,
  ⟨892, c892, 4000, checked892⟩,
  ⟨893, c893, 4000, checked893⟩,
  ⟨894, c894, 4000, checked894⟩,
  ⟨895, c895, 4000, checked895⟩,
  ⟨896, c896, 4000, checked896⟩,
  ⟨897, c897, 4000, checked897⟩,
  ⟨898, c898, 4000, checked898⟩,
  ⟨899, c899, 4000, checked899⟩,
  ⟨900, c900, 4000, checked900⟩,
  ⟨901, c901, 4000, checked901⟩]

end PA215.ContractShards.Shard006Part7
