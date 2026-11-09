module

public import PA213.FastResolve
public import PA213.SourceSites
public import PA213.SourceTrie
public import PA213.SourceCodes
public import PA215.Source.ExactTrie

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA213.SourceProgram
open PA215.Source PA215.Source.PathTrie PA213.FastResolve
def path (i : Nat) : Path := ((sites[i]?).map (·.path)).getD []
theorem sites_count : sites.size = 3947 := by decide +kernel
theorem codes_count : codes.size = 3947 := by decide +kernel
end PA213.SourceProgram
