module
public import I3_380.Engine.Arithmetic.ControlPorts
public import I3_380.Engine.Arithmetic.DecoderControl
public import I3_380.Engine.Arithmetic.RegisterSelection
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def marked (path : List Bool) (count : Nat) (gap : M)
    (before after : List M) : M :=
  cell root 1 (packWord path (repeatBit true (count : M)
    (repeatBit false gap (registers before (pushBit false (pushBit false (reverseRegisters after 0)))))))

theorem marked_initial (path : List Bool) (gap : M) (rs : List M) :
    marked path 0 gap rs [] = frame path gap rs := by
  simp only [marked,frame,Nat.cast_zero,repeatBit_zero,reverseRegisters,pushBit_false_zero]

/-- One selector pass changes the marked boundary while preserving
all register values. The gap and each register are model-valued. -/
theorem selectCycle {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute (M := M) path dec r) (n : Nat) (gap : M) (hn : n ≤ r.val)
    (before after : List M) (value : M) :
    Reaches referenceMachine (marked path n (gap+3) (before++[value]) after)
      (marked path (n+1) (gap+2) before (value::after)) := by
  let l := repeatBit true (n : M) (packWord path.reverse 1)
  let suffix := reverseRegisters after 0
  let box := registers (before++[value]) (pushBit false (pushBit false suffix))
  let moved := registers before (pushBit false (pushBit false
    (repeatBit true (value+1) (pushBit false suffix))))
  have start := route.run (repeatBit true (n : M) (repeatBit false (gap+3) box))
  have enter := enterSelector dec r.val n r.isLt hn (packWord path.reverse 1) (repeatBit false (gap+2) box)
  have splitGap : gap+3 = (gap+2)+1 := by
    have three : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
    rw [add_assoc,three]
  have gapTwo : gap+2 = (gap+1)+1 := by rw [add_assoc,one_add_one_eq_two]
  rw [splitGap,repeatBit_succ,gapTwo,repeatBit_succ] at start
  rw [gapTwo,repeatBit_succ] at enter
  have select := selectRegister (pushBit false l) gap before value suffix
  have next := left (show Row (breakPort false) false true false (dispatch 0) by decide +kernel)
    l (pushBit false (repeatBit false (gap+1) moved))
  rw [fromLeft_pushBit] at select
  have short : Engine.shortZeros 0 (Engine.ones n ++ path.reverse) = true := by
    rw [Engine.shortZeros_ones]
    exact route.short
  have back := dispatchFrom (Engine.ones n ++ path.reverse) 0 (by decide) short
    (pushBit true (pushBit false (repeatBit false (gap+1) moved)))
  rw [packWord_append,← repeatBit_cast] at back
  have pass := start.trans (enter.trans (select.trans (next.trans back)))
  rw [List.reverse_append,List.reverse_reverse,Engine.reverse_ones,packWord_append,← repeatBit_cast] at pass
  have repeatOne : repeatBit true (n : M)
      (pushBit true (pushBit false (repeatBit false (gap+1) moved))) =
    repeatBit true ((n : M)+1) (repeatBit false (gap+2) moved) := by
    simp only [repeatBit_push,repeatBit_succ,gapTwo]
  rw [repeatOne] at pass
  unfold marked
  rw [Nat.cast_succ,splitGap,repeatBit_succ,gapTwo,repeatBit_succ]
  simpa only [gapTwo,repeatBit_succ,reverseRegisters,moved] using pass

theorem selectPasses {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute (M := M) path dec r) (gap : M)
    (pending : List M) (n : Nat) (bound : n + pending.length ≤ r.val+1)
    (before after : List M) :
    Reaches referenceMachine (marked path n (gap+2+(pending.length : M)) (before++pending.reverse) after)
      (marked path (n+pending.length) (gap+2) before (pending.reverse++after)) := by
  induction pending generalizing n after with
  | nil => simpa using Reaches.refl referenceMachine (marked path n (gap+2) before after)
  | cons value pending ih =>
    let g := gap + (pending.length : M)
    have atThree : gap+2+((value::pending).length : M) = g+3 := by
      simp only [List.length_cons,Nat.cast_succ,g]
      have three : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
      rw [three]
      ac_rfl
    have atTwo : g+2 = gap+2+(pending.length : M) := by dsimp [g]; ac_rfl
    have remains : n+1+pending.length ≤ r.val+1 := by simp only [List.length_cons] at bound; omega
    rw [atThree,List.reverse_cons,← List.append_assoc]
    have pick := selectCycle route n g (by omega) (before++pending.reverse) after value
    rw [atTwo] at pick
    have rest := ih (n+1) remains (value::after)
    exact pick.trans (by
      simpa only [List.length_cons,show n+1+pending.length = n+(pending.length+1) by omega,
        List.append_assoc,List.singleton_append] using rest)

theorem selectFrame {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute (M := M) path dec r) (gap : M) (before after : List M) (value : M)
    (index : after.length = r.val) :
    Reaches referenceMachine (frame path (gap+2+((r.val+1 : Nat) : M)) (before++value::after))
      (marked path (r.val+1) (gap+2) before (value::after)) := by
  have len : (after.reverse++[value]).length = r.val+1 := by simp [index]
  have run := selectPasses route gap (after.reverse++[value]) 0 (by rw [len,Nat.zero_add]) before []
  simpa only [len,Nat.zero_add,List.reverse_append,List.reverse_singleton,List.reverse_reverse,
    List.singleton_append,List.append_nil,marked_initial] using run

end PalomarI3380.ArithmeticMachine.Reference
