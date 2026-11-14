module
public import PA196.ArithmeticSupport.Theory
public import PA196.ArithmeticSupport.Calibration.RelationalMultiplicationRewriting
public import PA196.ArithmeticSupport.Calibration.RelationalMultiplicationRecurrence
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

macro "mulCompactSyntax" : tactic => `(tactic|
  (simp only [mulPrevious,mulTotalProperty,mulPrefixExists,mulResult,mulRecurrence,
    mulPrefix_rew,addResult_rew,Ordinal.successor,graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

end M6.PA.RelationalSource.PairGraph
