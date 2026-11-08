import PA215PA.Theory
import PA213PA.InternalAXPlan
import PA215.Source.AXTypedFullPlan
namespace PA213.PA.InternalTrace.ModelAX
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- All276 actual macros, stopping before the separate35-row final gate. -/
theorem actual_pre_gate (v : Fin 6 → V) (tail bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (config 25 (materialize v tail Source.AXSymbolic.initial) bottom n)
      (config 3769 (materialize v tail Source.AXSymbolic.actualResult) bottom n) :=
  plan_positive Source.AXModelBounds.full_plan (by decide) _ _ (run_actual v tail) bottom n
#print axioms actual_pre_gate
end PA213.PA.InternalTrace.ModelAX

