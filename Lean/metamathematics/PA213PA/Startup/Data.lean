module

public import PA213PA.ZipNatTape
public import PA213.StartupExact
public import PA213.FastPaths

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.PA.Startup
abbrev startupFile := PA213.Startup.startupFile
def startupPath := PA213.FastPaths.path 68
def nativeFrame := PA213.Startup.startupTarget
def finalConfig := ZipNatTape.encode nativeFrame
 theorem encode_nativeFrame : ZipNatTape.encode nativeFrame=finalConfig := rfl
 theorem final_control : finalConfig.control=target 81 := by decide +kernel
 theorem final_left : finalConfig.left=1 := by decide +kernel
 theorem full_file_length : startupFile.length=64 := PA213.Startup.startup_file_length
 theorem blank_run_64764 : NatTape.run 64764 NatTape.blank=some finalConfig := by
  have h := ZipNatTape.run_forward 64764 PA213.Startup.blank PA213.Startup.startupTarget PA213.Startup.startup_exact
  have hb : ZipNatTape.encode PA213.Startup.blank = NatTape.blank := by decide +kernel
  rw [hb] at h
  exact h
#print axioms blank_run_64764
end PA213.PA.Startup
