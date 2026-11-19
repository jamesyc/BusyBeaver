module
public import M207.Startup.Data
public import M207.Permutation
@[expose] public section
namespace M207
open M6.Runtime
def start35 : SConf := (73, false, [.bit true], [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 42, .bit true, .box (.plain .none)])
end M207

namespace M207.Startup
open M6.Zip M6.Runtime
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

def initialFile : List Nat := [0,0,0,0,0,0,2,0,0] ++ List.replicate 26 1

theorem blank_exact : c0000 = zc 0 [] [] := by decide +kernel

theorem clean_exact : c0458 = mapConf forward (conc 0 initialFile start35) := by decide +kernel

end M207.Startup
