import PA215PA.RelationalPredicateTemplateTerms
namespace PA215.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] nthDef
 theorem lookup_correct (out b i : V) : nthDef.val.Evalb ![out,b,i] ↔ out=nth b i :=
  nth_defined.df ![out,b,i]
#print axioms lookup_correct
end PA215.PA.RelationalPredicateTemplate
