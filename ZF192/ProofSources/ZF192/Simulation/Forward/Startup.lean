module
public import ZF192.Simulation.Frames.Coverage
public import ZF192.Machine.Startup.Frame
public import ZF192Support.Execution.Registers.Scheduler.InitialComplete

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF192Support.NativeSource ZF192Support.NativeCommands
open M192.Calibration M192.Control

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem startup_pc_eq : align 25 = sourceStart.pc := by decide +kernel

theorem startup_registers_eq :
    permute (nativeInitial (M := M)).registers = fun i => (sourceStart.registers i : M) := by
  funext i
  rcases i with ⟨i, hi⟩
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases_i with h|h|h|h|h|h|h|h|h <;> subst i <;>
    simp [nativeInitial, permute, compilerSlot, sourceStart]

theorem physical_startup :
    ∃ hist p : M, BinaryTape.runHistory BinaryTape.blankCode hist ∧
      modelListHead hist = p ∧ FrameRelation (ZF192Support.NativeSource.stateCode (nativeInitial (M:=M))) p := by
  have h := BinaryTape.physical_reach_history (M:=M) (BinaryTape.zc 0 [] []) _ M192.Startup.blank_to_frame
  rw [BinaryTape.encode_frameN, ← BinaryTape.blankCode_encoded] at h
  obtain ⟨hist, hh, he⟩ := h
  refine ⟨hist, _, hh, he, 25, by decide, (M192.Startup.startupPadding : M),
    BinaryTape.bitsCode M192.Startup.rightTail, (nativeInitial (M := M)).registers, rfl, ?_⟩
  rw [startup_pc_eq, startup_registers_eq]

private theorem halt_frame {stop : ZF192Support.NativeSource.State M} (hstop : stop.pc = 10)
    (hist p : M) (hh : BinaryTape.runHistory BinaryTape.blankCode hist)
    (he : modelListHead hist = p) (hr : FrameRelation (ZF192Support.NativeSource.stateCode stop) p) :
    BinaryTape.physicalHalts (M:=M) := by
  obtain ⟨pc, hpc, n, ρ, regs, ha, hb⟩ := hr
  have hs := ZF192Support.NativeSource.stateCode_injective ha
  have hp : (pc:M) = (10:Nat) := by
    simpa [hstop] using (congrArg ZF192Support.NativeSource.State.pc hs).symm
  have hp' : pc = 10 := Nat.cast_inj.mp hp
  subst pc
  have row : compilerProgram 10 = some .halt := by decide +kernel
  obtain ⟨terminal, run, terminal_valid⟩ := aligned_halt hpc row regs n ρ
  obtain ⟨out, hout, head⟩ := run.reaches BinaryTape.blankCode hist hh (he.trans hb)
  exact ⟨out, hout, by simpa only [head] using terminal_valid⟩

/-- An internal C refutation gives an actual coded halting history, including
when that history has nonstandard length. -/
theorem literalCRefutation_physical (h : ZF192Support.ModelCommands.compilable (1:M)) :
    BinaryTape.physicalHalts (M:=M) := by
  obtain ⟨code, stop, hrun, hend, hstop⟩ := literalCRefutation_initial_native_history_unconditional h
  obtain ⟨hist, p, hHist, hHead, hInit⟩ := physical_startup (M:=M)
  obtain ⟨out, q, hout, hq, hrel⟩ := frame_history_lift _ code hrun _ hist p hHist hHead hInit
  rw [hend] at hrel
  exact halt_frame hstop out q hout hq hrel

end ZF192.NativePhysicalLift
