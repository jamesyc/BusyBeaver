module
public import M6.Source.Enumeration
public import ExactHistorySoundness
@[expose] public section
namespace C207Search
open C207Soundness
open M6.Source.Cantor

theorem pair_eq_cantor (a b : Nat) : pair a b = cantor a b := by
  simp only [pair, triangle_closed, cantor]
end C207Search
