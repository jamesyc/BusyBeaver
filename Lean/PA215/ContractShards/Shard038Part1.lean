import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C038
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard038Part1
open PA215.Contracts PA215.Census

def original4886 : RawOriginal := C038.records[22]'(by decide)
theorem original_id4886 : original4886.index = 4886 := by decide

def c4886 : Contract := original4886.toContract.get (by decide)
theorem binding4886 : original4886.toContract = some c4886 := rfl

theorem checked4886 : check 4000 c4886 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4887 : RawOriginal := C038.records[23]'(by decide)
theorem original_id4887 : original4887.index = 4887 := by decide

def c4887 : Contract := original4887.toContract.get (by decide)
theorem binding4887 : original4887.toContract = some c4887 := rfl

theorem checked4887 : check 4000 c4887 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4888 : RawOriginal := C038.records[24]'(by decide)
theorem original_id4888 : original4888.index = 4888 := by decide

def c4888 : Contract := original4888.toContract.get (by decide)
theorem binding4888 : original4888.toContract = some c4888 := rfl

theorem checked4888 : check 4000 c4888 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4889 : RawOriginal := C038.records[25]'(by decide)
theorem original_id4889 : original4889.index = 4889 := by decide

def c4889 : Contract := original4889.toContract.get (by decide)
theorem binding4889 : original4889.toContract = some c4889 := rfl

theorem checked4889 : check 4000 c4889 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4890 : RawOriginal := C038.records[26]'(by decide)
theorem original_id4890 : original4890.index = 4890 := by decide

def c4890 : Contract := original4890.toContract.get (by decide)
theorem binding4890 : original4890.toContract = some c4890 := rfl

theorem checked4890 : check 4000 c4890 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4891 : RawOriginal := C038.records[27]'(by decide)
theorem original_id4891 : original4891.index = 4891 := by decide

def c4891 : Contract := original4891.toContract.get (by decide)
theorem binding4891 : original4891.toContract = some c4891 := rfl

theorem checked4891 : check 4000 c4891 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4892 : RawOriginal := C038.records[28]'(by decide)
theorem original_id4892 : original4892.index = 4892 := by decide

def c4892 : Contract := original4892.toContract.get (by decide)
theorem binding4892 : original4892.toContract = some c4892 := rfl

theorem checked4892 : check 4000 c4892 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4893 : RawOriginal := C038.records[29]'(by decide)
theorem original_id4893 : original4893.index = 4893 := by decide

def c4893 : Contract := original4893.toContract.get (by decide)
theorem binding4893 : original4893.toContract = some c4893 := rfl

theorem checked4893 : check 4000 c4893 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4894 : RawOriginal := C038.records[30]'(by decide)
theorem original_id4894 : original4894.index = 4894 := by decide

def c4894 : Contract := original4894.toContract.get (by decide)
theorem binding4894 : original4894.toContract = some c4894 := rfl

theorem checked4894 : check 4000 c4894 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4895 : RawOriginal := C038.records[31]'(by decide)
theorem original_id4895 : original4895.index = 4895 := by decide

def c4895 : Contract := original4895.toContract.get (by decide)
theorem binding4895 : original4895.toContract = some c4895 := rfl

theorem checked4895 : check 4000 c4895 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4896 : RawOriginal := C038.records[32]'(by decide)
theorem original_id4896 : original4896.index = 4896 := by decide

def c4896 : Contract := original4896.toContract.get (by decide)
theorem binding4896 : original4896.toContract = some c4896 := rfl

theorem checked4896 : check 4000 c4896 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4897 : RawOriginal := C038.records[33]'(by decide)
theorem original_id4897 : original4897.index = 4897 := by decide

def c4897 : Contract := original4897.toContract.get (by decide)
theorem binding4897 : original4897.toContract = some c4897 := rfl

theorem checked4897 : check 4000 c4897 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4898 : RawOriginal := C038.records[34]'(by decide)
theorem original_id4898 : original4898.index = 4898 := by decide

def c4898 : Contract := original4898.toContract.get (by decide)
theorem binding4898 : original4898.toContract = some c4898 := rfl

theorem checked4898 : check 4000 c4898 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4899 : RawOriginal := C038.records[35]'(by decide)
theorem original_id4899 : original4899.index = 4899 := by decide

def c4899 : Contract := original4899.toContract.get (by decide)
theorem binding4899 : original4899.toContract = some c4899 := rfl

theorem checked4899 : check 4000 c4899 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4900 : RawOriginal := C038.records[36]'(by decide)
theorem original_id4900 : original4900.index = 4900 := by decide

def c4900 : Contract := original4900.toContract.get (by decide)
theorem binding4900 : original4900.toContract = some c4900 := rfl

theorem checked4900 : check 4000 c4900 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4901 : RawOriginal := C038.records[37]'(by decide)
theorem original_id4901 : original4901.index = 4901 := by decide

def c4901 : Contract := original4901.toContract.get (by decide)
theorem binding4901 : original4901.toContract = some c4901 := rfl

theorem checked4901 : check 4000 c4901 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4886, c4886, 4000, checked4886⟩,
  ⟨4887, c4887, 4000, checked4887⟩,
  ⟨4888, c4888, 4000, checked4888⟩,
  ⟨4889, c4889, 4000, checked4889⟩,
  ⟨4890, c4890, 4000, checked4890⟩,
  ⟨4891, c4891, 4000, checked4891⟩,
  ⟨4892, c4892, 4000, checked4892⟩,
  ⟨4893, c4893, 4000, checked4893⟩,
  ⟨4894, c4894, 4000, checked4894⟩,
  ⟨4895, c4895, 4000, checked4895⟩,
  ⟨4896, c4896, 4000, checked4896⟩,
  ⟨4897, c4897, 4000, checked4897⟩,
  ⟨4898, c4898, 4000, checked4898⟩,
  ⟨4899, c4899, 4000, checked4899⟩,
  ⟨4900, c4900, 4000, checked4900⟩,
  ⟨4901, c4901, 4000, checked4901⟩]

end PA215.ContractShards.Shard038Part1
