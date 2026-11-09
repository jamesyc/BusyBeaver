module

public import PA213.StartupData
public import PA211.UserCandidate.CandidateTable

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run112 : run machine 256 checkpoint112 = some checkpoint113 := by decide +kernel
theorem reach112 : Reach machine checkpoint112 checkpoint113 := ⟨256, run112⟩

theorem run113 : run machine 256 checkpoint113 = some checkpoint114 := by decide +kernel
theorem reach113 : Reach machine checkpoint113 checkpoint114 := ⟨256, run113⟩

theorem run114 : run machine 256 checkpoint114 = some checkpoint115 := by decide +kernel
theorem reach114 : Reach machine checkpoint114 checkpoint115 := ⟨256, run114⟩

theorem run115 : run machine 256 checkpoint115 = some checkpoint116 := by decide +kernel
theorem reach115 : Reach machine checkpoint115 checkpoint116 := ⟨256, run115⟩

theorem run116 : run machine 256 checkpoint116 = some checkpoint117 := by decide +kernel
theorem reach116 : Reach machine checkpoint116 checkpoint117 := ⟨256, run116⟩

theorem run117 : run machine 256 checkpoint117 = some checkpoint118 := by decide +kernel
theorem reach117 : Reach machine checkpoint117 checkpoint118 := ⟨256, run117⟩

theorem run118 : run machine 256 checkpoint118 = some checkpoint119 := by decide +kernel
theorem reach118 : Reach machine checkpoint118 checkpoint119 := ⟨256, run118⟩

theorem run119 : run machine 256 checkpoint119 = some checkpoint120 := by decide +kernel
theorem reach119 : Reach machine checkpoint119 checkpoint120 := ⟨256, run119⟩

theorem run120 : run machine 256 checkpoint120 = some checkpoint121 := by decide +kernel
theorem reach120 : Reach machine checkpoint120 checkpoint121 := ⟨256, run120⟩

theorem run121 : run machine 256 checkpoint121 = some checkpoint122 := by decide +kernel
theorem reach121 : Reach machine checkpoint121 checkpoint122 := ⟨256, run121⟩

theorem run122 : run machine 256 checkpoint122 = some checkpoint123 := by decide +kernel
theorem reach122 : Reach machine checkpoint122 checkpoint123 := ⟨256, run122⟩

theorem run123 : run machine 256 checkpoint123 = some checkpoint124 := by decide +kernel
theorem reach123 : Reach machine checkpoint123 checkpoint124 := ⟨256, run123⟩

theorem run124 : run machine 256 checkpoint124 = some checkpoint125 := by decide +kernel
theorem reach124 : Reach machine checkpoint124 checkpoint125 := ⟨256, run124⟩

theorem run125 : run machine 256 checkpoint125 = some checkpoint126 := by decide +kernel
theorem reach125 : Reach machine checkpoint125 checkpoint126 := ⟨256, run125⟩

theorem run126 : run machine 256 checkpoint126 = some checkpoint127 := by decide +kernel
theorem reach126 : Reach machine checkpoint126 checkpoint127 := ⟨256, run126⟩

theorem run127 : run machine 256 checkpoint127 = some checkpoint128 := by decide +kernel
theorem reach127 : Reach machine checkpoint127 checkpoint128 := ⟨256, run127⟩

end PA211.UserCandidate.Startup
