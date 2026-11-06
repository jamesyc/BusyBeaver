import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C023
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard023Part0
open PA215.Contracts PA215.Census

def original2950 : RawOriginal := C023.records[6]'(by decide)
theorem original_id2950 : original2950.index = 2950 := by decide

def c2950 : Contract := original2950.toContract.get (by decide)
theorem binding2950 : original2950.toContract = some c2950 := rfl

theorem checked2950 : check 4000 c2950 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2951 : RawOriginal := C023.records[7]'(by decide)
theorem original_id2951 : original2951.index = 2951 := by decide

def c2951 : Contract := original2951.toContract.get (by decide)
theorem binding2951 : original2951.toContract = some c2951 := rfl

theorem checked2951 : check 4000 c2951 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2952 : RawOriginal := C023.records[8]'(by decide)
theorem original_id2952 : original2952.index = 2952 := by decide

def c2952 : Contract := original2952.toContract.get (by decide)
theorem binding2952 : original2952.toContract = some c2952 := rfl

theorem checked2952 : check 4000 c2952 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2953 : RawOriginal := C023.records[9]'(by decide)
theorem original_id2953 : original2953.index = 2953 := by decide

def c2953 : Contract := original2953.toContract.get (by decide)
theorem binding2953 : original2953.toContract = some c2953 := rfl

theorem checked2953 : check 4000 c2953 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2954 : RawOriginal := C023.records[10]'(by decide)
theorem original_id2954 : original2954.index = 2954 := by decide

def c2954 : Contract := original2954.toContract.get (by decide)
theorem binding2954 : original2954.toContract = some c2954 := rfl

theorem checked2954 : check 4000 c2954 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2955 : RawOriginal := C023.records[11]'(by decide)
theorem original_id2955 : original2955.index = 2955 := by decide

def c2955 : Contract := original2955.toContract.get (by decide)
theorem binding2955 : original2955.toContract = some c2955 := rfl

theorem checked2955 : check 4000 c2955 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2956 : RawOriginal := C023.records[12]'(by decide)
theorem original_id2956 : original2956.index = 2956 := by decide

def c2956 : Contract := original2956.toContract.get (by decide)
theorem binding2956 : original2956.toContract = some c2956 := rfl

theorem checked2956 : check 4000 c2956 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2957 : RawOriginal := C023.records[13]'(by decide)
theorem original_id2957 : original2957.index = 2957 := by decide

def c2957 : Contract := original2957.toContract.get (by decide)
theorem binding2957 : original2957.toContract = some c2957 := rfl

theorem checked2957 : check 4000 c2957 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2958 : RawOriginal := C023.records[14]'(by decide)
theorem original_id2958 : original2958.index = 2958 := by decide

def c2958 : Contract := original2958.toContract.get (by decide)
theorem binding2958 : original2958.toContract = some c2958 := rfl

theorem checked2958 : check 4000 c2958 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2959 : RawOriginal := C023.records[15]'(by decide)
theorem original_id2959 : original2959.index = 2959 := by decide

def c2959 : Contract := original2959.toContract.get (by decide)
theorem binding2959 : original2959.toContract = some c2959 := rfl

theorem checked2959 : check 4000 c2959 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2960 : RawOriginal := C023.records[16]'(by decide)
theorem original_id2960 : original2960.index = 2960 := by decide

def c2960 : Contract := original2960.toContract.get (by decide)
theorem binding2960 : original2960.toContract = some c2960 := rfl

theorem checked2960 : check 4000 c2960 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2961 : RawOriginal := C023.records[17]'(by decide)
theorem original_id2961 : original2961.index = 2961 := by decide

def c2961 : Contract := original2961.toContract.get (by decide)
theorem binding2961 : original2961.toContract = some c2961 := rfl

theorem checked2961 : check 4000 c2961 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2962 : RawOriginal := C023.records[18]'(by decide)
theorem original_id2962 : original2962.index = 2962 := by decide

def c2962 : Contract := original2962.toContract.get (by decide)
theorem binding2962 : original2962.toContract = some c2962 := rfl

theorem checked2962 : check 4000 c2962 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2963 : RawOriginal := C023.records[19]'(by decide)
theorem original_id2963 : original2963.index = 2963 := by decide

def c2963 : Contract := original2963.toContract.get (by decide)
theorem binding2963 : original2963.toContract = some c2963 := rfl

theorem checked2963 : check 4000 c2963 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2964 : RawOriginal := C023.records[20]'(by decide)
theorem original_id2964 : original2964.index = 2964 := by decide

def c2964 : Contract := original2964.toContract.get (by decide)
theorem binding2964 : original2964.toContract = some c2964 := rfl

theorem checked2964 : check 4000 c2964 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2965 : RawOriginal := C023.records[21]'(by decide)
theorem original_id2965 : original2965.index = 2965 := by decide

def c2965 : Contract := original2965.toContract.get (by decide)
theorem binding2965 : original2965.toContract = some c2965 := rfl

theorem checked2965 : check 4000 c2965 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2950, c2950, 4000, checked2950⟩,
  ⟨2951, c2951, 4000, checked2951⟩,
  ⟨2952, c2952, 4000, checked2952⟩,
  ⟨2953, c2953, 4000, checked2953⟩,
  ⟨2954, c2954, 4000, checked2954⟩,
  ⟨2955, c2955, 4000, checked2955⟩,
  ⟨2956, c2956, 4000, checked2956⟩,
  ⟨2957, c2957, 4000, checked2957⟩,
  ⟨2958, c2958, 4000, checked2958⟩,
  ⟨2959, c2959, 4000, checked2959⟩,
  ⟨2960, c2960, 4000, checked2960⟩,
  ⟨2961, c2961, 4000, checked2961⟩,
  ⟨2962, c2962, 4000, checked2962⟩,
  ⟨2963, c2963, 4000, checked2963⟩,
  ⟨2964, c2964, 4000, checked2964⟩,
  ⟨2965, c2965, 4000, checked2965⟩]

end PA215.ContractShards.Shard023Part0
