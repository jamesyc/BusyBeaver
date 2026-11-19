module
public import PrimitiveUnpair
@[expose] public section
namespace C207Search.Primitive.Unpair
open M207.Source

private theorem row25 : program 25 = some (.dec 1 27 26) := by decide +kernel

theorem exit_not_terminal (s : Store) : scalarNext program (exitAt s) ≠ none := by
 unfold scalarNext exitAt
 rw [row25]
 simp only [Option.bind_some,scalarExecute]
 split <;> simp

end C207Search.Primitive.Unpair
