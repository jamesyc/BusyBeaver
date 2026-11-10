import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C038
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard038Part2
open PA215.Contracts PA215.Census

def original4902 : RawOriginal := C038.records[38]'(by decide)
theorem original_id4902 : original4902.index = 4902 := by decide

def c4902 : Contract := original4902.toContract.get (by decide)
theorem binding4902 : original4902.toContract = some c4902 := rfl

theorem checked4902 : check 4000 c4902 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4903 : RawOriginal := C038.records[39]'(by decide)
theorem original_id4903 : original4903.index = 4903 := by decide

def c4903 : Contract := original4903.toContract.get (by decide)
theorem binding4903 : original4903.toContract = some c4903 := rfl

theorem checked4903 : check 4000 c4903 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4904 : RawOriginal := C038.records[40]'(by decide)
theorem original_id4904 : original4904.index = 4904 := by decide

def c4904 : Contract := original4904.toContract.get (by decide)
theorem binding4904 : original4904.toContract = some c4904 := rfl

theorem checked4904 : check 4000 c4904 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4905 : RawOriginal := C038.records[41]'(by decide)
theorem original_id4905 : original4905.index = 4905 := by decide

def c4905 : Contract := original4905.toContract.get (by decide)
theorem binding4905 : original4905.toContract = some c4905 := rfl

theorem checked4905 : check 4000 c4905 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4906 : RawOriginal := C038.records[42]'(by decide)
theorem original_id4906 : original4906.index = 4906 := by decide

def c4906 : Contract := original4906.toContract.get (by decide)
theorem binding4906 : original4906.toContract = some c4906 := rfl

theorem checked4906 : check 4000 c4906 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4907 : RawOriginal := C038.records[43]'(by decide)
theorem original_id4907 : original4907.index = 4907 := by decide

def c4907 : Contract := original4907.toContract.get (by decide)
theorem binding4907 : original4907.toContract = some c4907 := rfl

theorem checked4907 : check 4000 c4907 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4908 : RawOriginal := C038.records[44]'(by decide)
theorem original_id4908 : original4908.index = 4908 := by decide

def c4908 : Contract := original4908.toContract.get (by decide)
theorem binding4908 : original4908.toContract = some c4908 := rfl

theorem checked4908 : check 4000 c4908 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4909 : RawOriginal := C038.records[45]'(by decide)
theorem original_id4909 : original4909.index = 4909 := by decide

def c4909 : Contract := original4909.toContract.get (by decide)
theorem binding4909 : original4909.toContract = some c4909 := rfl

theorem checked4909 : check 4000 c4909 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4910 : RawOriginal := C038.records[46]'(by decide)
theorem original_id4910 : original4910.index = 4910 := by decide

def c4910 : Contract := original4910.toContract.get (by decide)
theorem binding4910 : original4910.toContract = some c4910 := rfl

theorem checked4910 : check 4000 c4910 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4911 : RawOriginal := C038.records[47]'(by decide)
theorem original_id4911 : original4911.index = 4911 := by decide

def c4911 : Contract := original4911.toContract.get (by decide)
theorem binding4911 : original4911.toContract = some c4911 := rfl

theorem checked4911 : check 4000 c4911 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4912 : RawOriginal := C038.records[48]'(by decide)
theorem original_id4912 : original4912.index = 4912 := by decide

def c4912 : Contract := original4912.toContract.get (by decide)
theorem binding4912 : original4912.toContract = some c4912 := rfl

theorem checked4912 : check 4000 c4912 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4913 : RawOriginal := C038.records[49]'(by decide)
theorem original_id4913 : original4913.index = 4913 := by decide

def c4913 : Contract := original4913.toContract.get (by decide)
theorem binding4913 : original4913.toContract = some c4913 := rfl

theorem checked4913 : check 4000 c4913 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4914 : RawOriginal := C038.records[50]'(by decide)
theorem original_id4914 : original4914.index = 4914 := by decide

def c4914 : Contract := original4914.toContract.get (by decide)
theorem binding4914 : original4914.toContract = some c4914 := rfl

theorem checked4914 : check 4000 c4914 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4915 : RawOriginal := C038.records[51]'(by decide)
theorem original_id4915 : original4915.index = 4915 := by decide

def c4915 : Contract := original4915.toContract.get (by decide)
theorem binding4915 : original4915.toContract = some c4915 := rfl

theorem checked4915 : check 4000 c4915 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4916 : RawOriginal := C038.records[52]'(by decide)
theorem original_id4916 : original4916.index = 4916 := by decide

def c4916 : Contract := original4916.toContract.get (by decide)
theorem binding4916 : original4916.toContract = some c4916 := rfl

theorem checked4916 : check 4000 c4916 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4917 : RawOriginal := C038.records[53]'(by decide)
theorem original_id4917 : original4917.index = 4917 := by decide

def c4917 : Contract := original4917.toContract.get (by decide)
theorem binding4917 : original4917.toContract = some c4917 := rfl

theorem checked4917 : check 4000 c4917 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4902, c4902, 4000, checked4902⟩,
  ⟨4903, c4903, 4000, checked4903⟩,
  ⟨4904, c4904, 4000, checked4904⟩,
  ⟨4905, c4905, 4000, checked4905⟩,
  ⟨4906, c4906, 4000, checked4906⟩,
  ⟨4907, c4907, 4000, checked4907⟩,
  ⟨4908, c4908, 4000, checked4908⟩,
  ⟨4909, c4909, 4000, checked4909⟩,
  ⟨4910, c4910, 4000, checked4910⟩,
  ⟨4911, c4911, 4000, checked4911⟩,
  ⟨4912, c4912, 4000, checked4912⟩,
  ⟨4913, c4913, 4000, checked4913⟩,
  ⟨4914, c4914, 4000, checked4914⟩,
  ⟨4915, c4915, 4000, checked4915⟩,
  ⟨4916, c4916, 4000, checked4916⟩,
  ⟨4917, c4917, 4000, checked4917⟩]

end PA215.ContractShards.Shard038Part2
