module
public import FoundationSemanticCertificates
@[expose] public section
namespace ZFR
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

noncomputable def modelFiniteSet {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* BasicSetTheory] : List V → V
 | [] => ∅
 | x :: xs => insert x (modelFiniteSet xs)

end ZFR
