module
public import SearchSafety
@[expose] public section
namespace C209Search
open C209Soundness M6.Source.Cantor M6.Source.Enumeration

theorem ax_word_candidate_bound (a x y : Nat) (cs : List Command) :
 2 ≤ encodeWord (.ax a x y :: cs) 0 - 1 := by
 simp only [encodeWord,encodeCommand,Nat.add_sub_cancel]
 have hb := (pair_bounds (a+2) (pair y (pair x (encodeWord cs 0)))).1
 omega

end C209Search
