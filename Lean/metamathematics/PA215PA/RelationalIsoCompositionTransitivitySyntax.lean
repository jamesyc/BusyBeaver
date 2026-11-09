module

public import PA215PA.RelationalIsoCompositionExistsSyntax

@[expose] public section

namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

theorem compositionBijectionFreeEq (a b : Nat) :
    (orderBijection (.bvar 0) (.fvar a) (.fvar b) : Formula 1).free =
      orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1)) := by
  compositionSyntax

#print axioms compositionBijectionFreeEq
end PA215.PA.RelationalSource.PairGraph
