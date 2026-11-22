module
public import ZF192Support.Logic.Foundation.Axioms.Infinity
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- Every actual pinned BasicSetTheory axiom has an exact source-ZFR proof.
No theorem premise stands in for an axiom's derivation. -/
theorem source_bst_axiom {p : SetTheorySentence} (hp : BasicSetTheory p) :
 SourceTheorem (axiomSource p) := by
 cases hp with
 | equality p hp => exact source_equality_axiom hp
 | empty_set => exact source_bstEmpty
 | extensionality => exact source_bstExtensionality
 | pairing => exact source_bstPair
 | union => exact source_bstUnion
 | power_set => exact source_bstPower
 | infinity => exact source_bstInfinity
 | foundation => exact source_bstFoundation

end ZFR.FoundationBridge
