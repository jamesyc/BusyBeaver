import PA213.StartupData
import PA211.UserCandidate.CandidateTable
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run192 : run machine 256 checkpoint192 = some checkpoint193 := by decide +kernel
theorem reach192 : Reach machine checkpoint192 checkpoint193 := ⟨256, run192⟩

theorem run193 : run machine 256 checkpoint193 = some checkpoint194 := by decide +kernel
theorem reach193 : Reach machine checkpoint193 checkpoint194 := ⟨256, run193⟩

theorem run194 : run machine 256 checkpoint194 = some checkpoint195 := by decide +kernel
theorem reach194 : Reach machine checkpoint194 checkpoint195 := ⟨256, run194⟩

theorem run195 : run machine 256 checkpoint195 = some checkpoint196 := by decide +kernel
theorem reach195 : Reach machine checkpoint195 checkpoint196 := ⟨256, run195⟩

theorem run196 : run machine 256 checkpoint196 = some checkpoint197 := by decide +kernel
theorem reach196 : Reach machine checkpoint196 checkpoint197 := ⟨256, run196⟩

theorem run197 : run machine 256 checkpoint197 = some checkpoint198 := by decide +kernel
theorem reach197 : Reach machine checkpoint197 checkpoint198 := ⟨256, run197⟩

theorem run198 : run machine 256 checkpoint198 = some checkpoint199 := by decide +kernel
theorem reach198 : Reach machine checkpoint198 checkpoint199 := ⟨256, run198⟩

theorem run199 : run machine 256 checkpoint199 = some checkpoint200 := by decide +kernel
theorem reach199 : Reach machine checkpoint199 checkpoint200 := ⟨256, run199⟩

theorem run200 : run machine 256 checkpoint200 = some checkpoint201 := by decide +kernel
theorem reach200 : Reach machine checkpoint200 checkpoint201 := ⟨256, run200⟩

theorem run201 : run machine 256 checkpoint201 = some checkpoint202 := by decide +kernel
theorem reach201 : Reach machine checkpoint201 checkpoint202 := ⟨256, run201⟩

theorem run202 : run machine 256 checkpoint202 = some checkpoint203 := by decide +kernel
theorem reach202 : Reach machine checkpoint202 checkpoint203 := ⟨256, run202⟩

theorem run203 : run machine 256 checkpoint203 = some checkpoint204 := by decide +kernel
theorem reach203 : Reach machine checkpoint203 checkpoint204 := ⟨256, run203⟩

theorem run204 : run machine 256 checkpoint204 = some checkpoint205 := by decide +kernel
theorem reach204 : Reach machine checkpoint204 checkpoint205 := ⟨256, run204⟩

theorem run205 : run machine 256 checkpoint205 = some checkpoint206 := by decide +kernel
theorem reach205 : Reach machine checkpoint205 checkpoint206 := ⟨256, run205⟩

theorem run206 : run machine 256 checkpoint206 = some checkpoint207 := by decide +kernel
theorem reach206 : Reach machine checkpoint206 checkpoint207 := ⟨256, run206⟩

theorem run207 : run machine 256 checkpoint207 = some checkpoint208 := by decide +kernel
theorem reach207 : Reach machine checkpoint207 checkpoint208 := ⟨256, run207⟩

end PA211.UserCandidate.Startup
