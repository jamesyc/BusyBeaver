module

public import PA213.SourceProgramData

@[expose] public section
namespace PA213.ListBlocks
def blocks {α : Type} (l : List α) : Nat → List α
  | 0 => []
  | n+1 => blocks l n ++ (l.drop (n*64)).take 64
theorem blocks_eq_take {α : Type} (l : List α) (n : Nat) :
     blocks l n = l.take (n*64) := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    rw [blocks, ih]
    simpa only [Nat.succ_mul] using (List.take_add (l := l) (i := n*64) (j := 64)).symm
end PA213.ListBlocks
