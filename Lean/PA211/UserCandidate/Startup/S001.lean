module

public import PA213.StartupData
public import PA211.UserCandidate.CandidateTable

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run016 : run machine 256 checkpoint016 = some checkpoint017 := by decide +kernel
theorem reach016 : Reach machine checkpoint016 checkpoint017 := ⟨256, run016⟩

theorem run017 : run machine 256 checkpoint017 = some checkpoint018 := by decide +kernel
theorem reach017 : Reach machine checkpoint017 checkpoint018 := ⟨256, run017⟩

theorem run018 : run machine 256 checkpoint018 = some checkpoint019 := by decide +kernel
theorem reach018 : Reach machine checkpoint018 checkpoint019 := ⟨256, run018⟩

theorem run019 : run machine 256 checkpoint019 = some checkpoint020 := by decide +kernel
theorem reach019 : Reach machine checkpoint019 checkpoint020 := ⟨256, run019⟩

theorem run020 : run machine 256 checkpoint020 = some checkpoint021 := by decide +kernel
theorem reach020 : Reach machine checkpoint020 checkpoint021 := ⟨256, run020⟩

theorem run021 : run machine 256 checkpoint021 = some checkpoint022 := by decide +kernel
theorem reach021 : Reach machine checkpoint021 checkpoint022 := ⟨256, run021⟩

theorem run022 : run machine 256 checkpoint022 = some checkpoint023 := by decide +kernel
theorem reach022 : Reach machine checkpoint022 checkpoint023 := ⟨256, run022⟩

theorem run023 : run machine 256 checkpoint023 = some checkpoint024 := by decide +kernel
theorem reach023 : Reach machine checkpoint023 checkpoint024 := ⟨256, run023⟩

theorem run024 : run machine 256 checkpoint024 = some checkpoint025 := by decide +kernel
theorem reach024 : Reach machine checkpoint024 checkpoint025 := ⟨256, run024⟩

theorem run025 : run machine 256 checkpoint025 = some checkpoint026 := by decide +kernel
theorem reach025 : Reach machine checkpoint025 checkpoint026 := ⟨256, run025⟩

theorem run026 : run machine 256 checkpoint026 = some checkpoint027 := by decide +kernel
theorem reach026 : Reach machine checkpoint026 checkpoint027 := ⟨256, run026⟩

theorem run027 : run machine 256 checkpoint027 = some checkpoint028 := by decide +kernel
theorem reach027 : Reach machine checkpoint027 checkpoint028 := ⟨256, run027⟩

theorem run028 : run machine 256 checkpoint028 = some checkpoint029 := by decide +kernel
theorem reach028 : Reach machine checkpoint028 checkpoint029 := ⟨256, run028⟩

theorem run029 : run machine 256 checkpoint029 = some checkpoint030 := by decide +kernel
theorem reach029 : Reach machine checkpoint029 checkpoint030 := ⟨256, run029⟩

theorem run030 : run machine 256 checkpoint030 = some checkpoint031 := by decide +kernel
theorem reach030 : Reach machine checkpoint030 checkpoint031 := ⟨256, run030⟩

theorem run031 : run machine 256 checkpoint031 = some checkpoint032 := by decide +kernel
theorem reach031 : Reach machine checkpoint031 checkpoint032 := ⟨256, run031⟩

end PA211.UserCandidate.Startup
