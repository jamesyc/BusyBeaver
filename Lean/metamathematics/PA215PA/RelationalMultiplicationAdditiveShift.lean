module

public import PA215PA.RelationalMultiplicationFrame
public import PA215PA.RelationalAdditionApplications

@[expose] public section
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix mulPrefix

def mulAddOutputConclusionShift {Γ : List Form} (base : Nat)
    (h : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof (shifted Γ) (addOutputConclusion (base+1)) := by
  convert shiftProof h using 1 <;>
    (simp only [addOutputConclusion,addOutput]; mulCompactSyntax)

#print axioms mulAddOutputConclusionShift
end PA215.PA.RelationalSource.PairGraph
