module
public import I3_380.Search.Arithmetic.LogicalReplay
public import I3_380.Search.Arithmetic.SourceIteration
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine
open ArithmeticMachine.Reference (Frame bootFrame)
open Engine (LogicalState preparedStart)

def compactBoot : LogicalState :=
  ⟨[true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,false,true,false,false,true,false,true,true],
    [0,0,0,1,0,0,0,0,0,0,0,1]⟩

def compactInitial : LogicalState :=
  ⟨[],Store.file (fun _ : Register => (0 : Nat))⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem checked_compact_boot : advanceLogical 93 compactInitial = some compactBoot := by
  decide +kernel

def entryCheck (s : LogicalState) : Bool :=
  (trimPC s.path == []) && (List.ofFn (storeOf s.registers) == [1,0,0,0,0,0,0,0,0,0,0,0])

private theorem advanceLogical_add (n m : Nat) (s : LogicalState) :
    advanceLogical (n + m) s = (advanceLogical n s).bind (advanceLogical m) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, advanceLogical, Option.bind_some]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [advanceLogical]
    cases step : Engine.logicalNext s with
    | none => rfl
    | some t => exact ih t

private def entryCheckpoint (suffix : List Bool) : LogicalState :=
  ⟨List.replicate 12 true ++ false :: suffix, [0,0,0,0,0,0,0,0,0,0,0,1]⟩

private def entry128 : LogicalState :=
  entryCheckpoint (List.replicate 8 true ++ [false, true, true, true, true, true, true, false])

private def entry256 : LogicalState :=
  entryCheckpoint (List.replicate 11 true ++
    [false, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true])

section EntryReplay

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem boot_to_entry128 : advanceLogical 128 compactBoot = some entry128 := by
  decide +kernel

private theorem entry128_to_entry256 : advanceLogical 128 entry128 = some entry256 := by
  decide +kernel

private theorem entry256_to_root : (advanceLogical 52 entry256).any entryCheck = true := by
  decide +kernel

end EntryReplay

theorem checked_entry : (advanceLogical 308 compactBoot).any entryCheck = true := by
  change (advanceLogical (128 + (128 + 52)) compactBoot).any entryCheck = true
  rw [advanceLogical_add, boot_to_entry128, Option.bind_some,
    advanceLogical_add, entry128_to_entry256, Option.bind_some]
  exact entry256_to_root

attribute [local irreducible] preparedStart compactBoot

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def entryStore : Store M := fun r => if r = np then 1 else 0

theorem compactBoot_projects :
    projectFrame (bootFrame M) = project (logicalCast compactBoot) := by
  have full := advanceRegisters_logical Engine.bootstrap_exact.1
  have counts : 12 ≤ Engine.initialState.logical.registers.length := by
    change 12 ≤ Engine.initialState.registers.length
    simp only [Engine.initialState,List.length_append,List.length_replicate,List.length_singleton]
    decide
  have compactCount : 12 ≤ compactInitial.registers.length := by
    simp [compactInitial]
  have initial : project Engine.initialState.logical = project compactInitial := by
    change atPath [] (storeOf Engine.initialState.registers) =
      atPath [] (storeOf (Store.file (fun _ : Register => (0 : Nat))))
    rw [initial_store]
    exact congrArg (atPath []) (by simpa only [List.nil_append] using (storeOf_file [] (fun _ => (0 : Nat))).symm)
  have expected := advanceLogical_congr full checked_compact_boot counts compactCount initial
  have path : trimPC preparedStart.path = trimPC compactBoot.path :=
    congrArg PathState.pc expected
  have kept : storeOf preparedStart.registers = storeOf compactBoot.registers :=
    congrArg PathState.registers expected
  simp only [bootFrame,Frame.ofStandard,projectFrame,project,atPath,Frame.logical,logicalCast,
    storeOf_cast,path,kept]

theorem reachedAt_entry :
    ∃ stem : List M, 0 < stem.length ∧ ReachedAt (bootFrame M).code stem [] (entryStore (M := M)).code := by
  have verified := checked_entry
  cases result : advanceLogical 308 compactBoot with
  | none => simp [result] at verified
  | some logical =>
    have count : 12 ≤ compactBoot.registers.length := by unfold compactBoot; decide
    obtain ⟨finish,reach,ready,projection⟩ := advanceLogical_reaches result count
      (ArithmeticMachine.Reference.bootFrame_prepared (M := M)) compactBoot_projects
    obtain ⟨atRoot,registers⟩ : trimPC logical.path = [] ∧
        List.ofFn (storeOf logical.registers) = [1,0,0,0,0,0,0,0,0,0,0,0] := by
      simpa only [result,Option.any_some,entryCheck,Bool.and_eq_true,beq_iff_eq] using verified
    have expected : List.ofFn (entryStore (M := Nat)) = [1,0,0,0,0,0,0,0,0,0,0,0] := by
      decide +kernel
    have locals : storeOf logical.registers = entryStore (M := Nat) :=
      List.ofFn_injective (registers.trans expected.symm)
    have path : trimPC finish.path = [] :=
      (congrArg PathState.pc projection).trans atRoot
    have values : storeOf finish.values = entryStore (M := M) := by
      have values := congrArg PathState.registers projection
      change storeOf finish.values = storeOf (logical.registers.map Nat.cast) at values
      rw [storeOf_cast,locals] at values
      refine values.trans ?_
      funext r
      by_cases hr : r = np <;> simp [entryStore,hr,Function.comp_apply]
    obtain ⟨_,_,gap,span,record⟩ := reachedAt_of_frame finish ready reach
    let stem := finish.values.take (finish.values.length-12)
    refine ⟨stem,?_ ,Store.len_code _,Engine.clean_nil,gap,?_ ,?_⟩
    · have many := ready.2.1
      simp only [stem,List.length_take]
      omega
    · simpa only [path,show trimPC ([] : List Bool) = [] from rfl,List.length_nil,Nat.cast_zero,zero_add] using span
    · simpa only [values,frameFromCode,path,stem,show trimPC ([] : List Bool) = [] from rfl] using record

theorem CodedTermination.literal_halts (certified : CodedTermination (entryStore (M := M)).code) :
    (haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  obtain ⟨stem,nonempty,entry⟩ := reachedAt_entry (M := M)
  exact ArithmeticMachine.Reference.literal_halts_of_bootFrame (certified.reachesHalt nonempty entry)

end PalomarI3380.Compiler.Source
