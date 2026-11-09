module

public import PA213.StartupData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run080 : run machine 256 checkpoint080 = some checkpoint081 := by decide +kernel
theorem reach080 : Reach machine checkpoint080 checkpoint081 := ⟨256, run080⟩

theorem run081 : run machine 256 checkpoint081 = some checkpoint082 := by decide +kernel
theorem reach081 : Reach machine checkpoint081 checkpoint082 := ⟨256, run081⟩

theorem run082 : run machine 256 checkpoint082 = some checkpoint083 := by decide +kernel
theorem reach082 : Reach machine checkpoint082 checkpoint083 := ⟨256, run082⟩

theorem run083 : run machine 256 checkpoint083 = some checkpoint084 := by decide +kernel
theorem reach083 : Reach machine checkpoint083 checkpoint084 := ⟨256, run083⟩

theorem run084 : run machine 256 checkpoint084 = some checkpoint085 := by decide +kernel
theorem reach084 : Reach machine checkpoint084 checkpoint085 := ⟨256, run084⟩

theorem run085 : run machine 256 checkpoint085 = some checkpoint086 := by decide +kernel
theorem reach085 : Reach machine checkpoint085 checkpoint086 := ⟨256, run085⟩

theorem run086 : run machine 256 checkpoint086 = some checkpoint087 := by decide +kernel
theorem reach086 : Reach machine checkpoint086 checkpoint087 := ⟨256, run086⟩

theorem run087 : run machine 256 checkpoint087 = some checkpoint088 := by decide +kernel
theorem reach087 : Reach machine checkpoint087 checkpoint088 := ⟨256, run087⟩

theorem run088 : run machine 256 checkpoint088 = some checkpoint089 := by decide +kernel
theorem reach088 : Reach machine checkpoint088 checkpoint089 := ⟨256, run088⟩

theorem run089 : run machine 256 checkpoint089 = some checkpoint090 := by decide +kernel
theorem reach089 : Reach machine checkpoint089 checkpoint090 := ⟨256, run089⟩

theorem run090 : run machine 256 checkpoint090 = some checkpoint091 := by decide +kernel
theorem reach090 : Reach machine checkpoint090 checkpoint091 := ⟨256, run090⟩

theorem run091 : run machine 256 checkpoint091 = some checkpoint092 := by decide +kernel
theorem reach091 : Reach machine checkpoint091 checkpoint092 := ⟨256, run091⟩

theorem run092 : run machine 256 checkpoint092 = some checkpoint093 := by decide +kernel
theorem reach092 : Reach machine checkpoint092 checkpoint093 := ⟨256, run092⟩

theorem run093 : run machine 256 checkpoint093 = some checkpoint094 := by decide +kernel
theorem reach093 : Reach machine checkpoint093 checkpoint094 := ⟨256, run093⟩

theorem run094 : run machine 256 checkpoint094 = some checkpoint095 := by decide +kernel
theorem reach094 : Reach machine checkpoint094 checkpoint095 := ⟨256, run094⟩

theorem run095 : run machine 256 checkpoint095 = some checkpoint096 := by decide +kernel
theorem reach095 : Reach machine checkpoint095 checkpoint096 := ⟨256, run095⟩

end PA213.Startup
