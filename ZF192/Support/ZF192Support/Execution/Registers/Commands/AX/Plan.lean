module
public import ZF192Support.Execution.Registers.Commands.AX.SymbolicEval
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeAXSymbolic
open ZF192Support.NativeSource
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The simulation contract of a decoded list of AX operations. -/
def RealizesPlan (start : Nat) (ops : List Op) (stop : Nat) : Prop :=
  ∀ s s', run ops s = some s' → ∀ (n : M) (v : Fin 6 → M) (tail bottom : M),
    nativeReaches (NativeAX.config start n (materialize v tail bottom s))
      (NativeAX.config stop n (materialize v tail bottom s'))

private theorem run_append (xs ys : List Op) (s : Store) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append, run]
    cases h : exec op s <;> simp [ih]

theorem RealizesPlan.append {start mid stop : Nat} {xs ys : List Op}
    (left : RealizesPlan (M := M) start xs mid) (right : RealizesPlan (M := M) mid ys stop) :
    RealizesPlan (M := M) start (xs ++ ys) stop := by
  intro s s' he n v tail bottom
  rw [run_append] at he
  cases h : run xs s with
  | none => simp [h] at he
  | some between =>
    exact nativeReaches_trans (left s between h n v tail bottom)
      (right between s' (by simpa [h] using he) n v tail bottom)

end ZF192Support.NativeAXSymbolic
