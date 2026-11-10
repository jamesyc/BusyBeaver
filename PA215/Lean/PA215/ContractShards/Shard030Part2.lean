import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard030Part2
open PA215.Contracts PA215.Census

def original3878 : RawOriginal := C030.records[38]'(by decide)
theorem original_id3878 : original3878.index = 3878 := by decide

def c3878 : Contract := original3878.toContract.get (by decide)
theorem binding3878 : original3878.toContract = some c3878 := rfl

theorem checked3878 : check 4000 c3878 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3879 : RawOriginal := C030.records[39]'(by decide)
theorem original_id3879 : original3879.index = 3879 := by decide

def c3879 : Contract := original3879.toContract.get (by decide)
theorem binding3879 : original3879.toContract = some c3879 := rfl

theorem checked3879 : check 4000 c3879 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3880 : RawOriginal := C030.records[40]'(by decide)
theorem original_id3880 : original3880.index = 3880 := by decide

def c3880 : Contract := original3880.toContract.get (by decide)
theorem binding3880 : original3880.toContract = some c3880 := rfl

theorem checked3880 : check 4000 c3880 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3881 : RawOriginal := C030.records[41]'(by decide)
theorem original_id3881 : original3881.index = 3881 := by decide

def c3881 : Contract := original3881.toContract.get (by decide)
theorem binding3881 : original3881.toContract = some c3881 := rfl

theorem checked3881 : check 4000 c3881 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3882 : RawOriginal := C030.records[42]'(by decide)
theorem original_id3882 : original3882.index = 3882 := by decide

def c3882 : Contract := original3882.toContract.get (by decide)
theorem binding3882 : original3882.toContract = some c3882 := rfl

theorem checked3882 : check 4000 c3882 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3883 : RawOriginal := C030.records[43]'(by decide)
theorem original_id3883 : original3883.index = 3883 := by decide

def c3883 : Contract := original3883.toContract.get (by decide)
theorem binding3883 : original3883.toContract = some c3883 := rfl

theorem checked3883 : check 4000 c3883 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3884 : RawOriginal := C030.records[44]'(by decide)
theorem original_id3884 : original3884.index = 3884 := by decide

def c3884 : Contract := original3884.toContract.get (by decide)
theorem binding3884 : original3884.toContract = some c3884 := rfl

theorem checked3884 : check 4000 c3884 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3885 : RawOriginal := C030.records[45]'(by decide)
theorem original_id3885 : original3885.index = 3885 := by decide

def c3885 : Contract := original3885.toContract.get (by decide)
theorem binding3885 : original3885.toContract = some c3885 := rfl

theorem checked3885 : check 4000 c3885 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3886 : RawOriginal := C030.records[46]'(by decide)
theorem original_id3886 : original3886.index = 3886 := by decide

def c3886 : Contract := original3886.toContract.get (by decide)
theorem binding3886 : original3886.toContract = some c3886 := rfl

theorem checked3886 : check 4000 c3886 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3887 : RawOriginal := C030.records[47]'(by decide)
theorem original_id3887 : original3887.index = 3887 := by decide

def c3887 : Contract := original3887.toContract.get (by decide)
theorem binding3887 : original3887.toContract = some c3887 := rfl

theorem checked3887 : check 4000 c3887 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3888 : RawOriginal := C030.records[48]'(by decide)
theorem original_id3888 : original3888.index = 3888 := by decide

def c3888 : Contract := original3888.toContract.get (by decide)
theorem binding3888 : original3888.toContract = some c3888 := rfl

theorem checked3888 : check 4000 c3888 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3889 : RawOriginal := C030.records[49]'(by decide)
theorem original_id3889 : original3889.index = 3889 := by decide

def c3889 : Contract := original3889.toContract.get (by decide)
theorem binding3889 : original3889.toContract = some c3889 := rfl

theorem checked3889 : check 4000 c3889 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3890 : RawOriginal := C030.records[50]'(by decide)
theorem original_id3890 : original3890.index = 3890 := by decide

def c3890 : Contract := original3890.toContract.get (by decide)
theorem binding3890 : original3890.toContract = some c3890 := rfl

theorem checked3890 : check 4000 c3890 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3891 : RawOriginal := C030.records[51]'(by decide)
theorem original_id3891 : original3891.index = 3891 := by decide

def c3891 : Contract := original3891.toContract.get (by decide)
theorem binding3891 : original3891.toContract = some c3891 := rfl

theorem checked3891 : check 4000 c3891 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3892 : RawOriginal := C030.records[52]'(by decide)
theorem original_id3892 : original3892.index = 3892 := by decide

def c3892 : Contract := original3892.toContract.get (by decide)
theorem binding3892 : original3892.toContract = some c3892 := rfl

theorem checked3892 : check 4000 c3892 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3893 : RawOriginal := C030.records[53]'(by decide)
theorem original_id3893 : original3893.index = 3893 := by decide

def c3893 : Contract := original3893.toContract.get (by decide)
theorem binding3893 : original3893.toContract = some c3893 := rfl

theorem checked3893 : check 4000 c3893 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3878, c3878, 4000, checked3878⟩,
  ⟨3879, c3879, 4000, checked3879⟩,
  ⟨3880, c3880, 4000, checked3880⟩,
  ⟨3881, c3881, 4000, checked3881⟩,
  ⟨3882, c3882, 4000, checked3882⟩,
  ⟨3883, c3883, 4000, checked3883⟩,
  ⟨3884, c3884, 4000, checked3884⟩,
  ⟨3885, c3885, 4000, checked3885⟩,
  ⟨3886, c3886, 4000, checked3886⟩,
  ⟨3887, c3887, 4000, checked3887⟩,
  ⟨3888, c3888, 4000, checked3888⟩,
  ⟨3889, c3889, 4000, checked3889⟩,
  ⟨3890, c3890, 4000, checked3890⟩,
  ⟨3891, c3891, 4000, checked3891⟩,
  ⟨3892, c3892, 4000, checked3892⟩,
  ⟨3893, c3893, 4000, checked3893⟩]

end PA215.ContractShards.Shard030Part2
