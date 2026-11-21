module
public import I3_380.Engine.Arithmetic.StandardTape
public import I3_380.Engine.Arithmetic.DecoderSimulation
public import I3_380.Engine.Bootstrap
public import I3_380.Engine.Arithmetic.FrameExecution
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Reference

/-- Start the model-valued interpreter using the checked loader and
bootstrap trace. The register values here are the exact standard startup
values of the released interpreter. -/
theorem boot_reaches_frame :
    Reaches referenceMachine (0 : M)
      (frame Engine.preparedStart.path (Engine.preparedStart.gap : M)
        (Engine.preparedStart.registers.map Nat.cast)) := by
  have load : Engine.Reach blank loaderExit := ⟨39753,reference_startup⟩
  have warm : Engine.Reach loaderExit Engine.preparedStart.config := by
    rw [← Engine.initial_configuration]
    exact Engine.boot_ready.1
  obtain ⟨n,standardRun⟩ := load.trans warm
  have lifted := replay_of_run (M := M) referenceMachine standardRun
  rw [encodeLiteral_blank,Nat.cast_zero] at lifted
  exact ⟨(n : M),lifted.trans (frame_cast ..).symm⟩

noncomputable def Frame.ofStandard (s : Engine.RegisterState) : Frame M :=
  ⟨s.path,(s.gap : M),s.registers.map Nat.cast⟩

theorem Frame.ofStandard_prepared {s : Engine.RegisterState} (ready : s.Prepared) :
    (Frame.ofStandard (M := M) s).Prepared := by
  obtain ⟨clean,count,span⟩ := ready
  refine ⟨clean,by simpa only [Frame.ofStandard,List.length_map] using count,?_⟩
  change (74 : M) ≤ (s.path.length : M)+(s.gap : M)
  change 74 ≤ s.path.length+s.gap at span
  exact_mod_cast span

attribute [local irreducible] Engine.preparedStart

noncomputable def bootFrame (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Frame M :=
  Frame.ofStandard Engine.preparedStart

theorem bootFrame_prepared : (bootFrame M).Prepared :=
  Frame.ofStandard_prepared Engine.boot_ready.2

private theorem valid_blank : validReference decoderComparison (0 : M) := by
  have code : encode (↑(0 : Nat) : M) 0 0 = 0 := by simp [encode,Arithmetic.pair]
  rw [← code]
  refine (validReference_config decoderComparison 0 0 0 false (by simp [remIn])).mpr ?_
  exact ⟨by decide,by decide +kernel⟩

private theorem mapped_blank : mappedCode decoderComparison (0 : M) = 0 := by
  have code : encode (↑(0 : Nat) : M) 0 0 = 0 := by simp [encode,Arithmetic.pair]
  rw [← code,mappedCode_config]
  exact congrArg (fun q : Nat => encode (q : M) 0 0)
    (show decoderComparison.state 0 = 0 by decide +kernel)

theorem literal_halts_of_bootFrame (halt : ReachesHalt (bootFrame M).code) :
    (haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  obtain ⟨l,r,atHalt⟩ := halt
  have first : Reaches referenceMachine (0 : M) (bootFrame M).code := by
    unfold bootFrame Frame.ofStandard Frame.code
    exact boot_reaches_frame
  obtain ⟨time,finished⟩ := first.trans atHalt
  apply literal_halts_of_reference_arithmetic (0 : M) valid_blank
    ((mapped_blank (M := M)).symm ▸ Reaches.refl machine (0 : M)) time
  simp only [finished,cell,encode,Arithmetic.pi₁_pair]
  rfl

end Reference
end PalomarI3380.ArithmeticMachine
