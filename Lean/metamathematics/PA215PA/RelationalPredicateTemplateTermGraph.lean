module

public import PA215PA.RelationalPredicateTemplateLookupGraph

@[expose] public section
namespace PA215.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
noncomputable def termGraph {n : Nat} : Term n → 𝚺ᴬ₁.Semisentence 3
  | .bvar i => boundIndexGraph (i:Nat)
  | .fvar i => freeIndexGraph i
  | .func fn _ => nomatch fn
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem term_graph {n : Nat} (t : Term n) (out b f : V) :
    (termGraph t).val.Evalb ![out,b,f] ↔ out=termValue t b f := by
  cases t with
  | bvar i => exact boundIndex_graph (i:Nat) out b f
  | fvar i => exact freeIndex_graph i out b f
  | func fn _ => nomatch fn
#print axioms term_graph
end PA215.PA.RelationalPredicateTemplate
