module
public import ZF192Support.Coding.Histories.TraceEquations
public import ZF192Support.Coding.Histories.TraceFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelOperationalHistory
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Histories are internal reverse lists of coded stores: newest store first.
A singleton has no transition obligation; every later store extends its predecessor.
The relation must be an actual arithmetic transition, not an assumed execution oracle. -/
def edge (R : M → M → Prop) (next tail : M) : Prop :=
 tail=0 ∨ R (modelListHead tail) next

def history (R : M → M → Prop) (code : M) : Prop := modelTrace (edge R) code

end ZF192Support.ModelOperationalHistory
