module
public import I3_380.Search.Arithmetic.FrameReach
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (LogicalState Decoded logicalNext logicalDecoded)
open ArithmeticMachine (Reaches)
open ArithmeticMachine.Reference (Frame)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def logicalCast (s : LogicalState) : LogicalState M :=
  ⟨s.path,s.registers.map Nat.cast⟩

private theorem registerValue_cast (dec : Bool) (x : Nat) :
    Engine.registerValue dec (x : M) = (↑(Engine.registerValue dec x : Nat) : M) := by
  cases dec
  · simp [Engine.registerValue,Nat.cast_succ]
  · cases x with
    | zero => simp [Engine.registerValue]
    | succ x =>
      have positive : ((x+1 : Nat) : M) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero x)
      simp [Engine.registerValue,positive,Nat.cast_succ,add_tsub_cancel_right]

private theorem zeroDecrement_cast (dec : Bool) (x : Nat) :
    Engine.zeroDecrement dec (x : M) = Engine.zeroDecrement dec x := by
  simp [Engine.zeroDecrement,Nat.cast_eq_zero]

private theorem option_cast (value : Option Nat) :
    (value.map (Nat.cast : Nat → M)).getD 0 = (value.getD 0 : M) := by
  cases value <;> simp

theorem storeOf_cast (rs : List Nat) :
    storeOf (rs.map (Nat.cast : Nat → M)) = (Nat.cast : Nat → M) ∘ storeOf rs := by
  funext r
  simp [storeOf,option_cast,Function.comp_apply]

private theorem logicalDecoded_cast (rs : List Nat) (d : Decoded) :
    (logicalDecoded rs d).map (logicalCast (M := M)) = logicalDecoded (rs.map Nat.cast) d := by
  cases op : d.command with
  | halt | «break» => simp [logicalCast,logicalDecoded,op]
  | «continue» skip => cases skip <;> simp [logicalCast,logicalDecoded,op]
  | register dec r =>
    simp [logicalCast,logicalDecoded,op,option_cast,registerValue_cast,zeroDecrement_cast,List.map_set]

theorem logicalNext_cast (s : LogicalState) :
    (logicalNext s).map (logicalCast (M := M)) = logicalNext (logicalCast s) := by
  unfold logicalNext
  cases found : Engine.follow 59 Engine.Port.root [] (s.path ++ Engine.zeros 59) with
  | none => simp [logicalCast,found]
  | some d => simpa only [logicalCast,found,Option.bind_some] using logicalDecoded_cast (M := M) s.registers d

def advanceLogical : Nat → LogicalState → Option LogicalState
  | 0, s => some s
  | n+1, s => (logicalNext s).bind (advanceLogical n)

/-- Replay a standard prefix using only its logical states. The actual
tape reachability comes from the same model-valued interpreter proof
used for arbitrary search trials. -/
theorem advanceLogical_reaches {n : Nat} {s t : LogicalState} {physical : Frame M}
    (advance : advanceLogical n s = some t) (count : 12 ≤ s.registers.length)
    (prepared : physical.Prepared) (projects : projectFrame physical = project (logicalCast s)) :
    ∃ finish : Frame M, Reaches referenceMachine physical.code finish.code ∧
      finish.Prepared ∧ projectFrame finish = project (logicalCast t) := by
  induction n generalizing s physical with
  | zero =>
    have same : s = t := Option.some.inj advance
    exact ⟨physical,Reaches.refl ..,prepared,same ▸ projects⟩
  | succ n ih =>
    cases next : logicalNext s with
    | none => simp [advanceLogical,next] at advance
    | some mid =>
      have remaining : advanceLogical n mid = some t := by simpa only [advanceLogical,next,Option.bind_some] using advance
      have valid : 12 ≤ (logicalCast (M := M) s).registers.length := by simpa [logicalCast] using count
      have step := project_reference_step (logicalCast (M := M) s) valid
      rw [← logicalNext_cast,next,Option.map_some,Option.map_some,← projects] at step
      obtain ⟨middle,_,moved,ready,projected⟩ := advance_frame prepared step.symm
      obtain ⟨finish,tail,valid,eq⟩ := ih remaining (logical_count next count) ready projected
      exact ⟨finish,moved.trans tail,valid,eq⟩

theorem advanceRegisters_logical {n : Nat} {s t : Engine.RegisterState}
    (run : Engine.advanceRegisters n s = some t) :
    advanceLogical n s.logical = some t.logical := by
  induction n generalizing s with
  | zero =>
    have same : s = t := Option.some.inj run
    rw [same]
    rfl
  | succ n ih =>
    cases first : Engine.nextRegister s with
    | none => simp [Engine.advanceRegisters,first] at run
    | some mid =>
      have success : Engine.execute s ≠ .invalid := by
        intro invalid
        simp [Engine.nextRegister,invalid] at first
      have logical := Engine.logical_projection s success
      rw [first,Option.map_some] at logical
      have remaining : Engine.advanceRegisters n mid = some t := by
        simpa only [Engine.advanceRegisters,first,Option.bind_some] using run
      simpa only [advanceLogical,← logical,Option.bind_some] using ih remaining

theorem advanceLogical_congr {n : Nat} {s t other final : LogicalState}
    (first : advanceLogical n s = some t) (second : advanceLogical n other = some final)
    (sLength : 12 ≤ s.registers.length) (otherLength : 12 ≤ other.registers.length)
    (same : project s = project other) : project t = project final := by
  induction n generalizing s other with
  | zero =>
    cases (Option.some.inj first : s = t)
    cases (Option.some.inj second : other = final)
    exact same
  | succ n ih =>
    cases one : logicalNext s with
    | none => simp [advanceLogical,one] at first
    | some next =>
      cases two : logicalNext other with
      | none => simp [advanceLogical,two] at second
      | some next' =>
        have a := project_reference_step s sLength
        have b := project_reference_step other otherLength
        rw [one,Option.map_some,same,← b,two,Option.map_some] at a
        exact ih (by simpa only [advanceLogical,one,Option.bind_some] using first)
          (by simpa only [advanceLogical,two,Option.bind_some] using second)
          (logical_count one sLength) (logical_count two otherLength) (Option.some.inj a)

end PalomarI3380.Compiler
