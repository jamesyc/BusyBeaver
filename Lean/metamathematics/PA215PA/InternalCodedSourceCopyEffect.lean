import PA215PA.InternalCodedSourceCopy
namespace PA215.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma copyEnd_valid (r : Fin 9) (n xs : V) (hv : ValidStore xs) : ValidStore (copyEnd r n xs) :=
  drainEnd_valid 6 r n _ (drainTwoEnd_valid r 1 6 n xs hv)
#print axioms copyEnd_valid
end PA215.PA.InternalTrace.CodedSource
