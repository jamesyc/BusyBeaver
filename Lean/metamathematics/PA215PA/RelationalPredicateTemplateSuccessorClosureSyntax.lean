module

public import PA215PA.RelationalPredicateTemplateSuccessorSyntax
public import PA215PA.RelationalPredicateTemplateLiftSyntax
public import PA215PA.RelationalPredicateTemplateClosedCalibration
public import PA215PA.PAForwardRelationalArithmeticClosure
public import PA215PA.PAForwardRelationalRewriting

@[expose] public section
namespace PA215.PA.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder

theorem closure_lift : closure=liftFormula ForwardRelational.successorClosed := by
  have h : ForwardRelational.successorClosed=
      ∀¹ (RelationalSource.Ordinal.domain (.bvar 0) 🡒
        ∃¹ (RelationalSource.Ordinal.domain (.bvar 0) ⋏
          RelationalSource.Ordinal.successor (.bvar 1) (.bvar 0))) := by
    simp only [ForwardRelational.successorClosed,RelationalSource.closeParameter,
      RelationalSource.Ordinal.domainSuccessorStatement,RelationalSource.Ordinal.domainSuccessorExists,
      Semiformula.rewAux,Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux_neg,
      RelationalSource.Ordinal.domain_rew,RelationalSource.Ordinal.successor_rew]
    simp only [←Semiformula.neg_eq,Semiformula.rewAux_neg,RelationalSource.Ordinal.domain_rew]
    finishSuccessorSyntax
  rw [h]
  simp [closure,closureBody]


#print axioms closure_lift
end PA215.PA.RelationalPredicateTemplate.Successor
