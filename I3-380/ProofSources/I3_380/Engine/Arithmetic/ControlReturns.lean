module
public import I3_380.Engine.Arithmetic.ControlPorts
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row shortZeros breakPath breakPadding incrementReversed stripThrough)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pushMarker : pushBit true (0 : M) = 1 := by simp [pushBit]

theorem repeatZero_slide (n tail : M) :
    repeatBit false (n+1) tail = repeatBit false n (pushBit false tail) := by
  rw [repeatBit_push,repeatBit_succ]

private theorem breakBlank (skip : Bool) (y : M) :
    Reaches referenceMachine (fromLeft (breakPort skip) 1 y)
      (cell root 1 (repeatBit false ((breakPadding skip [] : Nat) : M) y)) := by
  cases skip with
  | false =>
    let source : DecoderWindow := ⟨⟨breakPort false,0,1⟩,10,1⟩
    let target : DecoderWindow := ⟨⟨root,1,0⟩,10,1⟩
    have trace : DecoderWindow.runToMatch referenceMachine target 16 source = some 16 := by decide +kernel
    refine ⟨(16 : Nat),?_⟩
    rw [← pushMarker,fromLeft_pushBit,pushMarker]
    simpa [source,target,windowCode,cell,pushBit,breakPadding,repeatBit_one,add_comm]
      using window_run trace (0 : M) y
  | true =>
    let source : DecoderWindow := ⟨⟨breakPort true,0,1⟩,10,1⟩
    let target : DecoderWindow := ⟨⟨root,1,0⟩,9,2⟩
    have trace : DecoderWindow.runToMatch referenceMachine target 17 source = some 17 := by decide +kernel
    refine ⟨(17 : Nat),?_⟩
    rw [← pushMarker,fromLeft_pushBit,pushMarker]
    have two : (2 : M) * 2 = 4 := by exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
    have after : repeatBit false 2 y = (4 : M)*y := by
      rw [← one_add_one_eq_two,repeatBit_succ,repeatBit_one]
      simp [pushBit,← mul_assoc,two]
    simpa [source,target,windowCode,cell,pushBit,breakPadding,after,add_comm]
      using window_run trace (0 : M) y

/-- Carry through the static instruction pointer and return to its
first bit. The zeros erased during the carry remain in the gap. -/
theorem breakRun (skip : Bool) (path : List Bool) (valid : shortZeros 0 path = true) (y : M) :
    Reaches referenceMachine (fromLeft (breakPort skip) (packWord path 1) y)
      (cell root 1 (packWord (breakPath skip path).reverse
        (repeatBit false ((breakPadding skip path : Nat) : M) y))) := by
  induction path generalizing skip y with
  | nil => cases skip <;> exact breakBlank _ y
  | cons b path ih =>
    have rest := Engine.shortZeros_tail valid
    change Reaches referenceMachine (fromLeft (breakPort skip) (pushBit b (packWord path 1)) y) _
    rw [fromLeft_pushBit]
    change Reaches referenceMachine (cell (breakPort skip) (packWord path 1) (pushBit b y)) _
    cases b <;> cases skip
    · have move := left (show Row (breakPort false) false true false (dispatch 0) by decide +kernel)
        (packWord path 1) y
      simpa only [breakPath,Bool.false_eq_true,↓reduceIte,incrementReversed,breakPadding,Nat.cast_zero,
        repeatBit_zero,List.reverse_cons,packWord_append,packWord_cons,packWord_nil] using
        move.trans (dispatchFrom path 0 (by decide) rest (pushBit true y))
    · have move := left (show Row (breakPort true) false false false (breakPort false) by decide +kernel)
        (packWord path 1) y
      simpa only [breakPath,Bool.false_eq_true,↓reduceIte,stripThrough,breakPadding,Nat.cast_succ,repeatZero_slide] using
        move.trans (ih false rest (pushBit false y))
    · have move := left (Engine.break_carry false) (packWord path 1) y
      simpa only [breakPath,Bool.false_eq_true,↓reduceIte,incrementReversed,breakPadding,Nat.add_zero,
        List.reverse_cons,packWord_append,packWord_cons,packWord_nil,repeatBit_push] using
        move.trans (ih false rest (pushBit false y))
    · have move := left (Engine.break_carry true) (packWord path 1) y
      simpa only [breakPath,↓reduceIte,stripThrough,Bool.true_eq_false,breakPadding,
        Nat.cast_succ,repeatZero_slide] using move.trans (ih true rest (pushBit false y))

/-- Erase up to and including the first one and return through the
remaining instruction bits. -/
theorem continueOne (path : List Bool) (valid : shortZeros 0 path = true)
    (hasOne : true ∈ path) (y : M) :
    Reaches referenceMachine (fromLeft Engine.Port.continueOne (packWord path 1) y)
      (cell root 1 (packWord (stripThrough true path).reverse
        (repeatBit false ((path.length - (stripThrough true path).length : Nat) : M) y))) := by
  induction path generalizing y with
  | nil => simp at hasOne
  | cons b path ih =>
    have rest := Engine.shortZeros_tail valid
    change Reaches referenceMachine (fromLeft Engine.Port.continueOne (pushBit b (packWord path 1)) y) _
    rw [fromLeft_pushBit]
    change Reaches referenceMachine (cell Engine.Port.continueOne (packWord path 1) (pushBit b y)) _
    cases b
    · have present : true ∈ path := by simpa using hasOne
      have bound := Engine.stripThrough_length true path
      have pad : path.length+1-(stripThrough true path).length =
          path.length-(stripThrough true path).length+1 := by omega
      have move := left (show Row Engine.Port.continueOne false false false Engine.Port.continueOne by decide +kernel)
        (packWord path 1) y
      simpa only [stripThrough,Bool.false_eq_true,↓reduceIte,List.length_cons,pad,Nat.cast_add,Nat.cast_one,repeatZero_slide]
        using move.trans (ih rest present (pushBit false y))
    · have pad : path.length+1-path.length = 1 := by omega
      have move := left (show Row Engine.Port.continueOne true false false (dispatch 0) by decide +kernel)
        (packWord path 1) y
      simpa only [stripThrough,↓reduceIte,List.length_cons,pad,Nat.cast_one,repeatBit_one] using
        move.trans (dispatchFrom path 0 (by decide) rest (pushBit false y))

end PalomarI3380.ArithmeticMachine.Reference
