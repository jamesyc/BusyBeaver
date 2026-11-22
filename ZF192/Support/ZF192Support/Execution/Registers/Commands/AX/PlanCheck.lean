module
public import ZF192Support.Execution.Registers.Commands.AX.Plan
public import ZF192Support.Execution.Registers.Commands.AX.Scan

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeAXSymbolic

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem op_sound {op : Op} {pc : Nat} (h : op.Valid pc) :
    Realizes (M:=M) op pc (op.next pc) := by
  cases op with
  | push => exact push_realizes h
  | cons => exact cons_realizes h.1 h.2.1 h.2.2
  | copyA => exact copyA_realizes h
  | copyD => exact copyD_realizes h
  | copyH => exact copyH_realizes h
  | incT => exact incT_realizes h.1 h.2
  | readD => obtain rfl : pc = 224 := h; exact readD_realizes
  | readH => obtain rfl : pc = 131 := h; exact readH_realizes

theorem checkPlan_sound {start stop : Nat} {ops : List Op}
    (checked : checkPlan start ops stop = true) : RealizesPlan (M := M) start ops stop := by
  induction ops generalizing start with
  | nil =>
    have eq : start = stop := by simpa [checkPlan] using checked
    subst stop
    intro s s' he n v tail bottom initial hist hh hl
    have eq : s = s' := Option.some.inj he
    subst s'
    exact ⟨hist, hh, hl⟩
  | cons op rest ih =>
    have facts : op.Valid start ∧ checkPlan (op.next start) rest stop = true := by
      simpa only [checkPlan, Bool.and_eq_true, decide_eq_true_eq] using checked
    intro s s' he n v tail bottom
    cases hx : exec op s with
    | none => simp [run, hx] at he
    | some between =>
      have he' : run rest between = some s' := by simpa [run, hx] using he
      exact ZF192Support.NativeSource.nativeReaches_trans
        (op_sound facts.1 s between hx n v tail bottom)
        (ih facts.2 between s' he' n v tail bottom)

end ZF192Support.NativeAXSymbolic
