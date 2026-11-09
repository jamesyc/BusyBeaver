module

public import PA215PA.PAInterpretedTheoryContext
public import PA215PA.PAForwardRelationalClosureSupport

@[expose] public section

/-! Discharge the closed-sentence support identity syntactically. -/
namespace PA215.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem ordinarySentenceSupport : SentenceImageSupport := by
  intro σ f
  apply formula_env_closed_source
  exact Semiformula.freeVariables_emb σ

def ordinaryFullRefutationDerivation
    (d : OrdinaryAnnotatedProof (Semiformula.falsum : Sentence Presentation.language)) :
    ND.Proof (ordinaryImageContext d.witnesses++interpretedFixedAxioms) ⊥ :=
  ordinaryRefutationDerivation d ordinarySentenceSupport

#print axioms ordinarySentenceSupport
#print axioms ordinaryFullRefutationDerivation
end PA215.PA.ForwardRelational
