module
public import I3_334Support.Engine.Arithmetic.Tape
public import I3_334Support.Machine.DecoderWindow
public import I3_334Support.Machine.Step
public import Mathlib.Tactic.Ring
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def windowCode (w : DecoderWindow) (leftTail rightTail : M) : M :=
  encode (w.config.state : M)
    ((w.config.left : M) + ((2^w.leftLength : Nat) : M) * leftTail)
    ((w.config.right : M) + ((2^w.rightLength : Nat) : M) * rightTail)

theorem tail_remainder (bits len : Nat) (tail : M) :
    remIn ((bits : M) + ((2^(len+1) : Nat) : M)*tail) 2 = (Nat.mod bits 2 : M) := by
  have cast := remIn_cast (M := M) bits 2
  rw [← cast]
  unfold remIn
  simp only [Nat.pow_succ',Nat.cast_mul,Nat.cast_ofNat,mul_assoc,add_comm (bits : M)]
  exact mod_mul_add' _ _ (by simp)

private theorem tail_div (bits len : Nat) (tail : M) :
    divIn ((bits : M) + ((2^(len+1) : Nat) : M)*tail) 2 = (Nat.div bits 2 : M) + ((2^len : Nat) : M)*tail := by
  rw [← divIn_cast (M := M) bits 2]
  unfold divIn
  simp only [Nat.pow_succ',Nat.cast_mul,Nat.cast_ofNat,mul_assoc,add_comm (bits : M)]
  rw [div_mul_add_self' _ _ (by simp),add_comm]

/-- A checked window step is valid with arbitrary arithmetic-model tails. -/
theorem window_tick {m : Machine} {w next : DecoderWindow}
    (edge : DecoderWindow.next m w = some next) (leftTail rightTail : M) :
    tick m.workingStates m.packedRows (windowCode w leftTail rightTail) =
      windowCode next leftTail rightTail := by
  rcases w with ⟨⟨q,l,r⟩,leftLen,rightLen⟩
  cases rightLen with
  | zero => simp [DecoderWindow.next] at edge
  | succ rightLen =>
    have working : q < m.workingStates := by
      by_contra outside
      have notWorking : m.workingStates ≤ q := Nat.le_of_not_gt outside
      cases leftLen <;> simp [DecoderWindow.next,PalomarI3380.step,notWorking] at edge
    let row := m.row q (Nat.mod r 2)
    let newState := Nat.div row 4
    let write := Nat.mod (Nat.div row 2) 2
    let l' : M := (l : M) + ((2^leftLen : Nat) : M) * leftTail
    let r' : M := (r : M) + ((2^(rightLen+1) : Nat) : M) * rightTail
    have arithWorking : (q : M) < (m.workingStates : M) := by exact_mod_cast working
    have arithRow : digit m.packedRows (q : M) r' = (row : M) := by
      rw [digit_at_row m,tail_remainder]
      have bits : Nat.mod r 2 = 0 ∨ Nat.mod r 2 = 1 := Nat.mod_two_eq_zero_or_one r
      rcases bits with h | h <;> simp [h,row]
    have state : divIn (row : M) 4 = (newState : M) := by
      simpa only [newState,Nat.cast_ofNat] using divIn_cast (M := M) row 4
    have written : remIn (divIn (row : M) 2) 2 = (write : M) := by
      have a := divIn_cast (M := M) row 2
      have b := remIn_cast (M := M) (Nat.div row 2) 2
      simpa only [write,Nat.cast_ofNat] using
        (congrArg (fun x => remIn x ((2 : Nat) : M)) a).trans b
    have moving : remIn (row : M) 2 = 1 ↔ Nat.mod row 2 = 1 := by
      rw [← Nat.cast_two,remIn_cast]
      exact Nat.cast_eq_one
    have rightDiv : divIn r' 2 = (Nat.div r 2 : M) + ((2^rightLen : Nat) : M)*rightTail :=
      tail_div r rightLen rightTail
    have physical : windowCode ⟨⟨q,l,r⟩,leftLen,rightLen+1⟩ leftTail rightTail =
        encode (q : M) l' r' := rfl
    rw [physical]
    by_cases direction : Nat.mod row 2 = 1
    · have rowAt : m.row q (Nat.mod r 2) = row := rfl
      have normal : step m ⟨q,l,r⟩ = some ⟨newState,2*l+write,Nat.div r 2⟩ := by
        simpa only [rowAt,newState,write,direction,↓reduceIte] using step_from_row m q l r working
      have after : next = ⟨⟨newState,2*l+write,Nat.div r 2⟩,leftLen+1,rightLen⟩ := by
        have well : m.row q (r % 2) % 2 = 1 := direction
        simpa only [DecoderWindow.next,well,↓reduceIte,normal,Option.map_some,Option.some.injEq,eq_comm] using edge
      rw [after]
      simp only [tick,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,arithWorking,↓reduceIte,
        arithRow,moving,direction,state,written,rightDiv]
      simp only [windowCode,l',Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.pow_succ']
      congr 2 <;> ring
    · cases leftLen with
      | zero =>
        have stays : ¬m.row q (r % 2) % 2 = 1 := direction
        simp [DecoderWindow.next,stays] at edge
      | succ leftLen =>
        have rowAt : m.row q (Nat.mod r 2) = row := rfl
        have normal : step m ⟨q,l,r⟩ =
            some ⟨newState,Nat.div l 2,4*Nat.div r 2+2*write+Nat.mod l 2⟩ := by
          simpa only [rowAt,newState,write,direction,↓reduceIte] using step_from_row m q l r working
        have after : next = ⟨⟨newState,Nat.div l 2,4*Nat.div r 2+2*write+Nat.mod l 2⟩,leftLen,rightLen+2⟩ := by
          have well : ¬m.row q (r % 2) % 2 = 1 := direction
          simpa only [DecoderWindow.next,well,↓reduceIte,normal,Option.map_some,Option.some.injEq,eq_comm] using edge
        have leftDiv : divIn l' 2 = (Nat.div l 2 : M) + ((2^leftLen : Nat) : M)*leftTail :=
          tail_div l leftLen leftTail
        have leftRem : remIn l' 2 = (Nat.mod l 2 : M) := tail_remainder l leftLen leftTail
        rw [after]
        simp only [tick,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,arithWorking,↓reduceIte,
          arithRow,moving,direction,state,written,rightDiv,leftDiv,leftRem]
        simp only [windowCode,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.pow_succ']
        congr 2 <;> ring

theorem window_run {m : Machine} {w goal : DecoderWindow} {fuel steps : Nat}
    (path : DecoderWindow.runToMatch m goal fuel w = some steps) (l r : M) :
    clock m.workingStates m.packedRows (steps : M) (windowCode w l r) = windowCode goal l r := by
  induction fuel generalizing w steps with
  | zero =>
    by_cases h : w = goal <;> simp [DecoderWindow.runToMatch,h] at path
    subst w steps
    simp
  | succ fuel ih =>
    by_cases h : w = goal
    · simp [DecoderWindow.runToMatch,h] at path
      subst w steps
      simp
    · cases move : DecoderWindow.next m w with
      | none => simp [DecoderWindow.runToMatch,h,move] at path
      | some n =>
        cases rest : DecoderWindow.runToMatch m goal fuel n with
        | none => simp [DecoderWindow.runToMatch,h,move,rest] at path
        | some k =>
          simp [DecoderWindow.runToMatch,h,move,rest] at path
          subst steps
          push_cast
          rw [add_comm (k : M) (1 : M),clock_add]
          rw [clock_one,window_tick move]
          exact ih rest

end PalomarI3380.ArithmeticMachine
