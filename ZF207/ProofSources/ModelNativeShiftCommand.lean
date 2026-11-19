module
public import ModelNativeGuard
public import ModelNativeUnpair
public import ModelNativeSStage
public import ModelNativeCommandBoundary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.NativeSStage ZF207.NativeGuard ZF207.ModelCommands ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def shiftFrame (n tail:M) (s:Store M) : Nat→M := fun i=>
 if i=0 then s.w else if i=1 then tail else if i=2 then s.h else if i=3 then s.d else if i=6 then n else 0
noncomputable def shiftStop (n tail:M) (s:Store M) : State M :=
 commandState 10 n tail 0 ⟨s.h,s.w,s.d,0⟩
lemma shift_stage_boundary (n tail:M) (s:Store M) :
 nativeReaches (bodyEntry .shift n tail s) (guardState (shiftFrame n tail s) 0 (s.t+s.h) 1) := by
 have h:=native_shift_stage (shiftFrame n tail s) s.t s.h
 simpa [stageState,guardState,shiftFrame,bodyEntry,commandState] using h
lemma shift_body_halt (n tail:M) (s:Store M) (he:s.t+s.h=1) :
 nativeReaches (bodyEntry .shift n tail s) (shiftStop n tail s) := by
 apply nativeReaches_trans (shift_stage_boundary n tail s)
 have h:=native_guard_equal (shiftFrame n tail s) (s.t+s.h) 1 he
 simpa [guardState,shiftStop,commandState,shiftFrame] using h
lemma shift_body_success (n tail:M) (s:Store M) (he:s.t+s.h≠1) :
 nativeReaches (bodyEntry .shift n tail s)
 (commandState 25 n tail 0 ⟨s.h,modelUnpairRight s.w,s.d,modelUnpairLeft s.w⟩) := by
 have guard:=native_guard_unequal (shiftFrame n tail s) (s.t+s.h) 1 he
 have u:=native_unpair (shiftFrame n tail s) s.w
 have u':nativeReaches (guardState (shiftFrame n tail s) 11 0 0)
  (commandState 25 n tail 0 ⟨s.h,modelUnpairRight s.w,s.d,modelUnpairLeft s.w⟩) := by
   simpa [guardState,unpairState,commandState,shiftFrame] using u
 exact nativeReaches_trans (shift_stage_boundary n tail s) (nativeReaches_trans guard u')
/-- Actual native SHIFT body executes the SAME arithmetic command evaluator.
The halt branch reaches literal instruction10, not exhausted scheduler state. -/
theorem native_shift_command (n tail:M) (s:Store M) :
 match modelCommandEval .shift s with
 | none => nativeReaches (bodyEntry .shift n tail s) (shiftStop n tail s)
 | some out => nativeReaches (bodyEntry .shift n tail s) (commandState 25 n tail 0 out) := by
 by_cases he:s.t+s.h=1
 · simpa only [modelCommandEval,if_pos he] using shift_body_halt n tail s he
 · simpa only [modelCommandEval,if_neg he] using shift_body_success n tail s he
end ZF207.NativeCommands
