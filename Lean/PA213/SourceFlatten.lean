module

public import PA213.SourceProgramData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA213.SourceProgram
open PA215.Source PA215.Source.PathTrie
theorem flatten_exact : flatten trie = sites.toList := by decide +kernel
end PA213.SourceProgram
