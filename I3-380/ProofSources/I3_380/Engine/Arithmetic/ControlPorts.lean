module
public import I3_380.Engine.Arithmetic.StandardTape
public import I3_380.Engine.Arithmetic.WindowReplay
public import I3_380.Engine.ControlWords
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row shortZeros)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] referenceMachine registerEntry

/-- Fewer than the requested number of marks sends the interpreter to
the selector. Only the standard control counter is traversed here. -/
theorem enterSelector (dec : Bool) (r n : Nat) (hr : r < 12) (hn : n ≤ r) (l x : M) :
    Reaches referenceMachine
      (cell (registerEntry dec r) l (repeatBit true (n : M) (pushBit false x)))
      (cell select (pushBit false (repeatBit true (n : M) l)) x) := by
  induction n generalizing r l with
  | zero => simpa only [Nat.cast_zero,repeatBit_zero] using right (Engine.entry_zero dec ⟨r,hr⟩) l x
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      have step := right (Engine.entry_advance dec ⟨r,by omega⟩) l
        (repeatBit true (n : M) (pushBit false x))
      have rest := ih r (by omega) (by omega) (pushBit true l)
      simpa only [Nat.cast_succ,repeatBit_succ,repeatBit_push] using step.trans rest

theorem enterOperation (dec : Bool) (r : Nat) (hr : r < 12) (l x : M) :
    Reaches referenceMachine
      (cell (registerEntry dec r) l (repeatBit true ((r : M)+1) x))
      (cell (registerOp dec) (repeatBit true ((r : M)+1) l) x) := by
  induction r generalizing l with
  | zero => simpa only [Nat.cast_zero,zero_add,repeatBit_one] using right (Engine.entry_operation dec) l x
  | succ r ih =>
    have step := right (Engine.entry_advance dec ⟨r,by omega⟩) l
      (repeatBit true ((r : M)+1) x)
    have rest := ih (by omega) (pushBit true l)
    simpa only [Nat.cast_succ,repeatBit_succ,repeatBit_push] using step.trans rest

private theorem dispatchBlank (y : M) :
    Reaches referenceMachine (fromLeft (dispatch 0) 0 (pushBit true y)) (cell root 1 y) := by
  let source : DecoderWindow := ⟨⟨dispatch 0,0,2⟩,7,2⟩
  let target : DecoderWindow := ⟨⟨root,1,0⟩,9,0⟩
  have trace : DecoderWindow.runToMatch referenceMachine target 14 source = some 14 := by decide +kernel
  refine ⟨14,?_⟩
  have h := window_run trace (0 : M) y
  simp only [source,target,windowCode,Nat.cast_zero,Nat.cast_one,mul_zero,add_zero,
    Nat.pow_zero,one_mul,zero_add,fromLeft,cell,pushBit,Bool.toNat_true,divIn,remIn,Arithmetic.zero_div,Arithmetic.zero_mod] at h ⊢
  have four : ((2^2 : Nat) : M) = 4 := by norm_num
  have two : (2 : M) * 2 = 4 := by exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
  simpa only [mul_add,mul_one,← mul_assoc,two,four,add_comm (2 : M),zero_add,add_zero,
    Nat.cast_ofNat] using h

/-- Return through a read-only finite path without inspecting its model-valued suffix. -/
theorem dispatchFrom (path : List Bool) (seen : Nat) (limit : seen ≤ 6)
    (valid : shortZeros seen path = true) (y : M) :
    Reaches referenceMachine
      (fromLeft (dispatch seen) (packWord path 1) y)
      (cell root 1 (packWord path.reverse y)) := by
  have marker : (1 : M) = pushBit true 0 := by simp [pushBit]
  induction path generalizing seen y with
  | nil =>
    change Reaches referenceMachine (fromLeft (dispatch seen) 1 y) (cell root 1 y)
    have move := left (Engine.dispatch_one ⟨seen,by omega⟩) (0 : M) y
    have start : fromLeft (dispatch seen) 1 y = cell (dispatch seen) 0 (pushBit true y) := by
      rw [marker,fromLeft_pushBit]
      rfl
    rw [start]
    exact move.trans (dispatchBlank y)
  | cons b path ih =>
    change Reaches referenceMachine
      (fromLeft (dispatch seen) (pushBit b (packWord path 1)) y)
      (cell root 1 (packWord (b :: path).reverse y))
    rw [fromLeft_pushBit,List.reverse_cons,packWord_append]
    cases b
    · obtain ⟨below,rest⟩ : seen < 6 ∧ shortZeros (seen+1) path = true := by simpa [shortZeros] using valid
      exact (left (Engine.dispatch_zero ⟨seen,below⟩) (packWord path 1) y).trans
        (ih (seen+1) (by omega) rest (pushBit false y))
    · exact (left (Engine.dispatch_one ⟨seen,by omega⟩) (packWord path 1) y).trans
        (ih 0 (by decide) valid (pushBit true y))

end PalomarI3380.ArithmeticMachine.Reference
