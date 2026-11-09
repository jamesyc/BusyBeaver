import PA213.StartupData
import PA211.UserCandidate.CandidateTable
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run048 : run machine 256 checkpoint048 = some checkpoint049 := by decide +kernel
theorem reach048 : Reach machine checkpoint048 checkpoint049 := ⟨256, run048⟩

theorem run049 : run machine 256 checkpoint049 = some checkpoint050 := by decide +kernel
theorem reach049 : Reach machine checkpoint049 checkpoint050 := ⟨256, run049⟩

theorem run050 : run machine 256 checkpoint050 = some checkpoint051 := by decide +kernel
theorem reach050 : Reach machine checkpoint050 checkpoint051 := ⟨256, run050⟩

theorem run051 : run machine 256 checkpoint051 = some checkpoint052 := by decide +kernel
theorem reach051 : Reach machine checkpoint051 checkpoint052 := ⟨256, run051⟩

theorem run052 : run machine 256 checkpoint052 = some checkpoint053 := by decide +kernel
theorem reach052 : Reach machine checkpoint052 checkpoint053 := ⟨256, run052⟩

theorem run053 : run machine 256 checkpoint053 = some checkpoint054 := by decide +kernel
theorem reach053 : Reach machine checkpoint053 checkpoint054 := ⟨256, run053⟩

theorem run054 : run machine 256 checkpoint054 = some checkpoint055 := by decide +kernel
theorem reach054 : Reach machine checkpoint054 checkpoint055 := ⟨256, run054⟩

theorem run055 : run machine 256 checkpoint055 = some checkpoint056 := by decide +kernel
theorem reach055 : Reach machine checkpoint055 checkpoint056 := ⟨256, run055⟩

theorem run056 : run machine 256 checkpoint056 = some checkpoint057 := by decide +kernel
theorem reach056 : Reach machine checkpoint056 checkpoint057 := ⟨256, run056⟩

theorem run057 : run machine 256 checkpoint057 = some checkpoint058 := by decide +kernel
theorem reach057 : Reach machine checkpoint057 checkpoint058 := ⟨256, run057⟩

theorem run058 : run machine 256 checkpoint058 = some checkpoint059 := by decide +kernel
theorem reach058 : Reach machine checkpoint058 checkpoint059 := ⟨256, run058⟩

theorem run059 : run machine 256 checkpoint059 = some checkpoint060 := by decide +kernel
theorem reach059 : Reach machine checkpoint059 checkpoint060 := ⟨256, run059⟩

theorem run060 : run machine 256 checkpoint060 = some checkpoint061 := by decide +kernel
theorem reach060 : Reach machine checkpoint060 checkpoint061 := ⟨256, run060⟩

theorem run061 : run machine 256 checkpoint061 = some checkpoint062 := by decide +kernel
theorem reach061 : Reach machine checkpoint061 checkpoint062 := ⟨256, run061⟩

theorem run062 : run machine 256 checkpoint062 = some checkpoint063 := by decide +kernel
theorem reach062 : Reach machine checkpoint062 checkpoint063 := ⟨256, run062⟩

theorem run063 : run machine 256 checkpoint063 = some checkpoint064 := by decide +kernel
theorem reach063 : Reach machine checkpoint063 checkpoint064 := ⟨256, run063⟩

end PA211.UserCandidate.Startup
