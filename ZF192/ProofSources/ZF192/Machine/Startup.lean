module
public import ZF192.Machine.Startup.Chunk1
public import ZF192.Machine.Startup.Chunk2
public import ZF192.Machine.Startup.Chunk3
public import ZF192.Machine.Startup.Chunk4
public import ZF192.Machine.Startup.Chunk5

@[expose] public section

namespace M192.Startup
open BinaryTape

private theorem join {m n : Nat} {a b c : Packed}
    (first : packedRun m a = some b) (second : packedRun n b = some c) :
    packedRun (m+n) a = some c := by
  rw [packedRun_add, first]
  exact second

set_option maxRecDepth 40000

/-- Exact run from the blank tape through all five checked intervals. -/
theorem startup_exact : run literal 44181 (zc 0 [] []) = some (unpack checkpoint5) := by
  have replay := join (join chunk1 chunk2) (join chunk3 (join chunk4 chunk5))
  exact checkedBlankRun (n := 44181) (final := checkpoint5) replay

end M192.Startup
