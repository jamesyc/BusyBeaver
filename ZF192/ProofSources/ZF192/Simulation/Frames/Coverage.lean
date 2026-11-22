module
public import ZF192.Simulation.Frames.Step
public import ZF192.Simulation.Frames.Relation

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF192.BinaryTape M192.Control
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem frame_step_contract : StepContract (FrameRelation (M := M)) := by
  intro a b q hs hr root hist valid head
  obtain ⟨s, t, rfl, rfl, pc, hpc, hspc, code, hcode, exec⟩ := hs
  obtain ⟨k, hk, n, ρ, regs, hsc, hq⟩ := hr
  have state : s = ⟨(k : M), regs⟩ := ZF192Support.NativeSource.stateCode_injective hsc
  have same : k = pc := Nat.cast_inj.mp (state.symm ▸ hspc)
  subst k
  subst s
  obtain ⟨pc', bounded, counter, n', moved⟩ := execute_aligned hpc hcode regs n ρ t exec
  obtain ⟨out, history, last⟩ := moved.reaches root hist valid (head.trans hq)
  refine ⟨out, _, history, last, pc', bounded, n', ρ, t.registers, ?_, rfl⟩
  have eq : (⟨(pc' : M), t.registers⟩ : ZF192Support.NativeSource.State M) = t := by
    cases t
    simp_all
  rw [eq]

theorem frame_history_lift (initial code : M) : Simulation FrameRelation initial code :=
  native_history_lift frameRelationGraph FrameRelation frameRelationGraph_eval
    frame_step_contract initial code

end ZF192.NativePhysicalLift
