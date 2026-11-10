import PA213.StartupData
import PA211.UserCandidate.CandidateTable
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run208 : run machine 256 checkpoint208 = some checkpoint209 := by decide +kernel
theorem reach208 : Reach machine checkpoint208 checkpoint209 := ⟨256, run208⟩

theorem run209 : run machine 256 checkpoint209 = some checkpoint210 := by decide +kernel
theorem reach209 : Reach machine checkpoint209 checkpoint210 := ⟨256, run209⟩

theorem run210 : run machine 256 checkpoint210 = some checkpoint211 := by decide +kernel
theorem reach210 : Reach machine checkpoint210 checkpoint211 := ⟨256, run210⟩

theorem run211 : run machine 256 checkpoint211 = some checkpoint212 := by decide +kernel
theorem reach211 : Reach machine checkpoint211 checkpoint212 := ⟨256, run211⟩

theorem run212 : run machine 256 checkpoint212 = some checkpoint213 := by decide +kernel
theorem reach212 : Reach machine checkpoint212 checkpoint213 := ⟨256, run212⟩

theorem run213 : run machine 256 checkpoint213 = some checkpoint214 := by decide +kernel
theorem reach213 : Reach machine checkpoint213 checkpoint214 := ⟨256, run213⟩

theorem run214 : run machine 256 checkpoint214 = some checkpoint215 := by decide +kernel
theorem reach214 : Reach machine checkpoint214 checkpoint215 := ⟨256, run214⟩

theorem run215 : run machine 256 checkpoint215 = some checkpoint216 := by decide +kernel
theorem reach215 : Reach machine checkpoint215 checkpoint216 := ⟨256, run215⟩

theorem run216 : run machine 256 checkpoint216 = some checkpoint217 := by decide +kernel
theorem reach216 : Reach machine checkpoint216 checkpoint217 := ⟨256, run216⟩

theorem run217 : run machine 256 checkpoint217 = some checkpoint218 := by decide +kernel
theorem reach217 : Reach machine checkpoint217 checkpoint218 := ⟨256, run217⟩

theorem run218 : run machine 256 checkpoint218 = some checkpoint219 := by decide +kernel
theorem reach218 : Reach machine checkpoint218 checkpoint219 := ⟨256, run218⟩

theorem run219 : run machine 256 checkpoint219 = some checkpoint220 := by decide +kernel
theorem reach219 : Reach machine checkpoint219 checkpoint220 := ⟨256, run219⟩

theorem run220 : run machine 256 checkpoint220 = some checkpoint221 := by decide +kernel
theorem reach220 : Reach machine checkpoint220 checkpoint221 := ⟨256, run220⟩

theorem run221 : run machine 256 checkpoint221 = some checkpoint222 := by decide +kernel
theorem reach221 : Reach machine checkpoint221 checkpoint222 := ⟨256, run221⟩

theorem run222 : run machine 256 checkpoint222 = some checkpoint223 := by decide +kernel
theorem reach222 : Reach machine checkpoint222 checkpoint223 := ⟨256, run222⟩

theorem run223 : run machine 256 checkpoint223 = some checkpoint224 := by decide +kernel
theorem reach223 : Reach machine checkpoint223 checkpoint224 := ⟨256, run223⟩

end PA211.UserCandidate.Startup
