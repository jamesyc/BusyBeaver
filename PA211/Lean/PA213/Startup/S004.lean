import PA213.StartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run064 : run machine 256 checkpoint064 = some checkpoint065 := by decide +kernel
theorem reach064 : Reach machine checkpoint064 checkpoint065 := ⟨256, run064⟩

theorem run065 : run machine 256 checkpoint065 = some checkpoint066 := by decide +kernel
theorem reach065 : Reach machine checkpoint065 checkpoint066 := ⟨256, run065⟩

theorem run066 : run machine 256 checkpoint066 = some checkpoint067 := by decide +kernel
theorem reach066 : Reach machine checkpoint066 checkpoint067 := ⟨256, run066⟩

theorem run067 : run machine 256 checkpoint067 = some checkpoint068 := by decide +kernel
theorem reach067 : Reach machine checkpoint067 checkpoint068 := ⟨256, run067⟩

theorem run068 : run machine 256 checkpoint068 = some checkpoint069 := by decide +kernel
theorem reach068 : Reach machine checkpoint068 checkpoint069 := ⟨256, run068⟩

theorem run069 : run machine 256 checkpoint069 = some checkpoint070 := by decide +kernel
theorem reach069 : Reach machine checkpoint069 checkpoint070 := ⟨256, run069⟩

theorem run070 : run machine 256 checkpoint070 = some checkpoint071 := by decide +kernel
theorem reach070 : Reach machine checkpoint070 checkpoint071 := ⟨256, run070⟩

theorem run071 : run machine 256 checkpoint071 = some checkpoint072 := by decide +kernel
theorem reach071 : Reach machine checkpoint071 checkpoint072 := ⟨256, run071⟩

theorem run072 : run machine 256 checkpoint072 = some checkpoint073 := by decide +kernel
theorem reach072 : Reach machine checkpoint072 checkpoint073 := ⟨256, run072⟩

theorem run073 : run machine 256 checkpoint073 = some checkpoint074 := by decide +kernel
theorem reach073 : Reach machine checkpoint073 checkpoint074 := ⟨256, run073⟩

theorem run074 : run machine 256 checkpoint074 = some checkpoint075 := by decide +kernel
theorem reach074 : Reach machine checkpoint074 checkpoint075 := ⟨256, run074⟩

theorem run075 : run machine 256 checkpoint075 = some checkpoint076 := by decide +kernel
theorem reach075 : Reach machine checkpoint075 checkpoint076 := ⟨256, run075⟩

theorem run076 : run machine 256 checkpoint076 = some checkpoint077 := by decide +kernel
theorem reach076 : Reach machine checkpoint076 checkpoint077 := ⟨256, run076⟩

theorem run077 : run machine 256 checkpoint077 = some checkpoint078 := by decide +kernel
theorem reach077 : Reach machine checkpoint077 checkpoint078 := ⟨256, run077⟩

theorem run078 : run machine 256 checkpoint078 = some checkpoint079 := by decide +kernel
theorem reach078 : Reach machine checkpoint078 checkpoint079 := ⟨256, run078⟩

theorem run079 : run machine 256 checkpoint079 = some checkpoint080 := by decide +kernel
theorem reach079 : Reach machine checkpoint079 checkpoint080 := ⟨256, run079⟩

end PA213.Startup
