module
public import M207.SourceTreeData

@[expose] public section

namespace M207.Source

/-- Resolve an instruction directly in the shared primitive tree. -/
def program (i : Nat) : Option Instruction :=
  if i < 4341 then TreeSource.resolve TreeSource.sourceTree i else none

/-- The corresponding route from the root to the source site. -/
def paths (i : Nat) : List Bool :=
  if i < 4341 then TreeSource.treePath TreeSource.sourceTree i else []

end M207.Source
