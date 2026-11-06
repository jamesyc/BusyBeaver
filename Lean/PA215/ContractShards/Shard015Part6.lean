import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part6
open PA215.Contracts PA215.Census

def original2022 : RawOriginal := C015.records[102]'(by decide)
theorem original_id2022 : original2022.index = 2022 := by decide

def c2022 : Contract := original2022.toContract.get (by decide)
theorem binding2022 : original2022.toContract = some c2022 := rfl

theorem checked2022 : check 4000 c2022 = true := by decide

def original2023 : RawOriginal := C015.records[103]'(by decide)
theorem original_id2023 : original2023.index = 2023 := by decide

def c2023 : Contract := original2023.toContract.get (by decide)
theorem binding2023 : original2023.toContract = some c2023 := rfl

theorem checked2023 : check 4000 c2023 = true := by decide

def original2024 : RawOriginal := C015.records[104]'(by decide)
theorem original_id2024 : original2024.index = 2024 := by decide

def c2024 : Contract := original2024.toContract.get (by decide)
theorem binding2024 : original2024.toContract = some c2024 := rfl

theorem checked2024 : check 4000 c2024 = true := by decide

def original2025 : RawOriginal := C015.records[105]'(by decide)
theorem original_id2025 : original2025.index = 2025 := by decide

def c2025 : Contract := original2025.toContract.get (by decide)
theorem binding2025 : original2025.toContract = some c2025 := rfl

theorem checked2025 : check 4000 c2025 = true := by decide

def original2026 : RawOriginal := C015.records[106]'(by decide)
theorem original_id2026 : original2026.index = 2026 := by decide

def c2026 : Contract := original2026.toContract.get (by decide)
theorem binding2026 : original2026.toContract = some c2026 := rfl

theorem checked2026 : check 4000 c2026 = true := by decide

def original2027 : RawOriginal := C015.records[107]'(by decide)
theorem original_id2027 : original2027.index = 2027 := by decide

def c2027 : Contract := original2027.toContract.get (by decide)
theorem binding2027 : original2027.toContract = some c2027 := rfl

theorem checked2027 : check 4000 c2027 = true := by decide

def original2028 : RawOriginal := C015.records[108]'(by decide)
theorem original_id2028 : original2028.index = 2028 := by decide

def c2028 : Contract := original2028.toContract.get (by decide)
theorem binding2028 : original2028.toContract = some c2028 := rfl

theorem checked2028 : check 4000 c2028 = true := by decide

def original2029 : RawOriginal := C015.records[109]'(by decide)
theorem original_id2029 : original2029.index = 2029 := by decide

def c2029 : Contract := original2029.toContract.get (by decide)
theorem binding2029 : original2029.toContract = some c2029 := rfl

theorem checked2029 : check 4000 c2029 = true := by decide

def original2030 : RawOriginal := C015.records[110]'(by decide)
theorem original_id2030 : original2030.index = 2030 := by decide

def c2030 : Contract := original2030.toContract.get (by decide)
theorem binding2030 : original2030.toContract = some c2030 := rfl

theorem checked2030 : check 4000 c2030 = true := by decide

def original2031 : RawOriginal := C015.records[111]'(by decide)
theorem original_id2031 : original2031.index = 2031 := by decide

def c2031 : Contract := original2031.toContract.get (by decide)
theorem binding2031 : original2031.toContract = some c2031 := rfl

theorem checked2031 : check 4000 c2031 = true := by decide

def original2032 : RawOriginal := C015.records[112]'(by decide)
theorem original_id2032 : original2032.index = 2032 := by decide

def c2032 : Contract := original2032.toContract.get (by decide)
theorem binding2032 : original2032.toContract = some c2032 := rfl

theorem checked2032 : check 4000 c2032 = true := by decide

def original2033 : RawOriginal := C015.records[113]'(by decide)
theorem original_id2033 : original2033.index = 2033 := by decide

def c2033 : Contract := original2033.toContract.get (by decide)
theorem binding2033 : original2033.toContract = some c2033 := rfl

theorem checked2033 : check 4000 c2033 = true := by decide

def original2034 : RawOriginal := C015.records[114]'(by decide)
theorem original_id2034 : original2034.index = 2034 := by decide

def c2034 : Contract := original2034.toContract.get (by decide)
theorem binding2034 : original2034.toContract = some c2034 := rfl

theorem checked2034 : check 4000 c2034 = true := by decide

def original2035 : RawOriginal := C015.records[115]'(by decide)
theorem original_id2035 : original2035.index = 2035 := by decide

def c2035 : Contract := original2035.toContract.get (by decide)
theorem binding2035 : original2035.toContract = some c2035 := rfl

theorem checked2035 : check 4000 c2035 = true := by decide

def original2036 : RawOriginal := C015.records[116]'(by decide)
theorem original_id2036 : original2036.index = 2036 := by decide

def c2036 : Contract := original2036.toContract.get (by decide)
theorem binding2036 : original2036.toContract = some c2036 := rfl

theorem checked2036 : check 4000 c2036 = true := by decide

def original2037 : RawOriginal := C015.records[117]'(by decide)
theorem original_id2037 : original2037.index = 2037 := by decide

def c2037 : Contract := original2037.toContract.get (by decide)
theorem binding2037 : original2037.toContract = some c2037 := rfl

theorem checked2037 : check 4000 c2037 = true := by decide

def records : List Certified := [
  ⟨2022, c2022, 4000, checked2022⟩,
  ⟨2023, c2023, 4000, checked2023⟩,
  ⟨2024, c2024, 4000, checked2024⟩,
  ⟨2025, c2025, 4000, checked2025⟩,
  ⟨2026, c2026, 4000, checked2026⟩,
  ⟨2027, c2027, 4000, checked2027⟩,
  ⟨2028, c2028, 4000, checked2028⟩,
  ⟨2029, c2029, 4000, checked2029⟩,
  ⟨2030, c2030, 4000, checked2030⟩,
  ⟨2031, c2031, 4000, checked2031⟩,
  ⟨2032, c2032, 4000, checked2032⟩,
  ⟨2033, c2033, 4000, checked2033⟩,
  ⟨2034, c2034, 4000, checked2034⟩,
  ⟨2035, c2035, 4000, checked2035⟩,
  ⟨2036, c2036, 4000, checked2036⟩,
  ⟨2037, c2037, 4000, checked2037⟩]

end PA215.ContractShards.Shard015Part6
