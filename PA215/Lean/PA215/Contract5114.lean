import PA215.HaltContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Contract5114
open PA215.Runtime PA215.NativeTable PA215.HaltContracts

def initial : SConf := (84, false, [.run true 0 1], [.run true 0 5, .run false 0 1, .run true 0 1, .run false 1 57, .run true 0 1, .box (.plain .none)])

theorem checked : check 4000 none initial = true := by decide

theorem uniform (n : Nat) (vs : List Nat) (hl : 10 ≤ vs.length) :
    PA215.Zip.Halts machine (conc n vs initial) :=
  sound 4000 none initial checked n vs ⟨hl, trivial⟩

end PA215.Contract5114
