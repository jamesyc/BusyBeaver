module
public import I3_334.Calibration.ModelProgram
public import I3_334.Simulation.MachineSimulation
public import I3_334Support.Search.Arithmetic.RegisterCast
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers_cast)
open Stock (Frame preparedFrame bootFrame advanceBootstrap)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

private def pathBits (bits : String) : List Bool := bits.toList.map (· == '1')

private def entry176 : Frame Nat :=
  bootFrame (pathBits "11111101111100111") 115 [0,0,0,0,0,0,0,0,0,0,1]

private def entry240 : Frame Nat :=
  bootFrame (pathBits "11111101111111100111111") 157 [2,0,0,0,0,0,0,0,0,0,1]

private def entry304 : Frame Nat :=
  bootFrame (pathBits "11111101111111111111110011101") 203 [1,0,0,0,0,0,0,0,0,0,1]

def entryFrame : Frame Nat :=
  bootFrame (List.replicate 12 false) 241 [0,0,0,0,0,0,0,0,0,0,1]

section EntryReplay
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000

private theorem entry_first : advanceBootstrap 64 preparedFrame = some entry176 := by decide +kernel
private theorem entry_second : advanceBootstrap 64 entry176 = some entry240 := by decide +kernel
private theorem entry_third : advanceBootstrap 64 entry240 = some entry304 := by decide +kernel
private theorem entry_fourth : advanceBootstrap 21 entry304 = some entryFrame := by decide +kernel

end EntryReplay

theorem checked_entry : advanceBootstrap 213 preparedFrame = some entryFrame := by
  change advanceBootstrap (64 + (64 + (64 + 21))) preparedFrame = _
  rw [Stock.advance_add, entry_first, Option.bind_some, Stock.advance_add, entry_second,
    Option.bind_some, Stock.advance_add, entry_third, Option.bind_some]
  exact entry_fourth

theorem literal_entry : ∃ time, run machine time blank = some entryFrame.config := by
  obtain ⟨before, boot, ready⟩ := literal_prepared_boot
  obtain ⟨reaches, _, _⟩ := literal_bootstrap ready.1 ready.2.1 checked_entry
  rw [Frame.code_nat, Frame.code_nat] at reaches
  obtain ⟨after, runTo⟩ := reach_of_arithmetic reaches (by decide)
  exact ⟨before+after, join_run boot runTo⟩

def entryStore {M : Type} [OfNat M 0] [OfNat M 1] : Store M :=
  fun r => if r = np then 1 else 0

private theorem entry_values : storeOf entryFrame.values = entryStore (M := Nat) := by
  have same : ∀ r : Register, storeOf entryFrame.values r = entryStore (M := Nat) r := by
    decide +kernel
  exact funext same

private theorem entry_path : trimPC entryFrame.path = [] := by decide +kernel

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def castFrame (s : Frame Nat) : Frame M :=
  ⟨s.path, (s.gap : M), s.values.map Nat.cast⟩

theorem castFrame_code (s : Frame Nat) : (castFrame (M := M) s).code = (encodeLiteral s.config : M) := by
  unfold castFrame Frame.code Stock.frame
  rw [registers_cast, repeatBit_cast, ← packWord_append, ← packWord_append, packWord_bits]
  simpa only [Frame.config, encodeLiteral, cell, Engine.zeros, List.append_assoc, Nat.cast_one] using
    encode_cast (M := M) Control.root 1
      (Engine.bits (s.path ++ (Engine.zeros s.gap ++ Engine.registers s.values)))

theorem reachedAt_entry :
    ∃ stem : List M, 0 < stem.length ∧ ModelFrame.ReachedAt 0 stem [] (entryStore (M := M)).code := by
  obtain ⟨time,actual⟩ := literal_entry
  have reaches : Reaches machine (0 : M) (castFrame entryFrame).code := by
    refine ⟨(time : M),?_⟩
    rw [castFrame_code, ← show (encodeLiteral blank : M) = 0 by simp]
    exact replay_of_run machine actual
  let ready := castFrame (M := M) entryFrame
  have before : ready.path = List.replicate 12 false := rfl
  have clean : Decoder.Clean ready.path := ⟨[],12,rfl,trivial⟩
  have count : 13 ≤ ready.values.length := by
    change 13 ≤ (entryFrame.values.map Nat.cast).length
    rw [List.length_map]
    decide +kernel
  have margin : (84 : M) ≤ ready.span := by
    change (84 : M) ≤ ((12 : Nat) : M) + (241 : M)
    norm_num
    exact Or.inr (by exact_mod_cast (show (84 : Nat) < 253 by decide))
  have prepared : ready.Prepared := ⟨clean,count,margin⟩
  have decoded := ModelFrame.reachedAt_of_frame ready prepared reaches
  have values : storeOf ready.values = entryStore (M := M) := by
    rw [show ready.values = entryFrame.values.map Nat.cast from rfl, storeOf_cast, entry_values]
    funext r
    by_cases isFirst : r = np <;> simp [entryStore, isFirst]
  rw [values] at decoded
  have cleanAddr : trimPC ready.path = trimPC [] := entry_path
  have reachRoot := ModelFrame.reachedAt_path cleanAddr decoded
  refine ⟨ready.values.take (ready.values.length-12),?_,reachRoot⟩
  simp only [List.length_take]
  omega

theorem CodedTermination.literal_halts (certified : CodedTermination (entryStore (M := M)).code) :
    (haltsDef 334 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  obtain ⟨stem,nonempty,entry⟩ := reachedAt_entry (M := M)
  obtain ⟨l,r,k,terminal⟩ := certified.reachesHalt nonempty entry
  apply (haltsDef_eval _ _).mpr
  refine ⟨k,?_⟩
  change ¬π₁ (clock machine.workingStates machine.packedRows k 0) < (334 : M)
  rw [terminal]
  simp [cell, encode]

end PalomarI3334.SearchProgram
