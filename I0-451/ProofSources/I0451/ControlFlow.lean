module
public import I0451.InstructionGraph

/-! Address effects of the control signals. Internal left and right
returns agree with the same jumps made by the literal dispatcher. -/
@[expose] public section
namespace I0451.Runtime

def skipDelimiters : Nat → Bool → List Bool → Option (List Bool)
  | 0, _, word => some word
  | n + 1, bit, word =>
    (cutAddress bit word).bind fun pair => skipDelimiters n bit pair.2

@[simp] theorem skip_matching (n : Nat) (bit : Bool) (rest : List Bool) :
    skipDelimiters (n + 1) bit (bit :: rest) = skipDelimiters n bit rest := by
  simp [skipDelimiters, cutAddress]

theorem skip_other (n : Nat) {bit read : Bool} (different : read ≠ bit) (rest : List Bool) :
    skipDelimiters (n + 1) bit (read :: rest) = skipDelimiters (n + 1) bit rest := by
  simp only [skipDelimiters, cutAddress, ite_eq_right different]
  cases cutAddress bit rest <;> rfl

/-- The address after a signal, packed with implicit right blanks. -/
def returnAddress (signal : Signal) (rev : List Bool) : Option Nat :=
  match signal with
  | .normal => some (pack (carry rev).reverse 0)
  | .break n => (skipDelimiters (n + 1) false rev).map (fun rest => pack (carry rest).reverse 0)
  | .restart n => (skipDelimiters (n + 1) true rev).map (fun rest => pack rest.reverse 0)
  | .halt => none

theorem return_normal_left (rev : List Bool) :
    returnAddress .normal (false :: rev) = some (pack (rev.reverse ++ [true]) 0) := by
  simp only [returnAddress, carry, List.reverse_cons]

theorem return_restart_right (rev : List Bool) :
    returnAddress (.restart 0) (true :: rev) = some (pack rev.reverse 0) := by
  simp [returnAddress, skipDelimiters, cutAddress]

theorem return_left {signal outer : Signal} (h : signal.leftExit = some outer) (rev : List Bool) :
    returnAddress signal (false :: rev) = returnAddress outer rev := by
  cases signal with
  | normal => contradiction
  | «break» n =>
    cases n with
    | zero =>
      simp only [Signal.leftExit, Option.some.injEq] at h
      subst outer
      simp [returnAddress, skipDelimiters, cutAddress]
    | succ n =>
      simp only [Signal.leftExit, Option.some.injEq] at h
      subst outer
      simp [returnAddress]
  | restart n =>
    simp only [Signal.leftExit, Option.some.injEq] at h
    subst outer
    simp only [returnAddress, skip_other n (by decide : false ≠ true)]
  | halt =>
    simp only [Signal.leftExit, Option.some.injEq] at h
    subst outer
    rfl

theorem return_right {signal outer : Signal} (h : signal.rightExit = some outer) (rev : List Bool) :
    returnAddress signal (true :: rev) = returnAddress outer rev := by
  cases signal with
  | normal =>
    simp only [Signal.rightExit, Option.some.injEq] at h
    subst outer
    simp only [returnAddress, carry, List.reverse_cons, pack_append]
    rfl
  | «break» n =>
    simp only [Signal.rightExit, Option.some.injEq] at h
    subst outer
    simp only [returnAddress, skip_other n (by decide : true ≠ false)]
  | restart n =>
    cases n with
    | zero => contradiction
    | succ n =>
      simp only [Signal.rightExit, Option.some.injEq] at h
      subst outer
      simp only [returnAddress, skip_matching]
  | halt =>
    simp only [Signal.rightExit, Option.some.injEq] at h
    subst outer
    rfl

/-- A decoder prefix designates a subtree or a terminal instruction. -/
def follow (start : Cursor) : List Bool → Option Edge
  | [] => some (.branch start)
  | b :: bs =>
    match outgoing start b with
    | none => none
    | some (.branch next) => follow next bs
    | some (.instruction op) => if bs.isEmpty then some (.instruction op) else none

def AtEdge (word : List Bool) (edge : Edge) : Prop :=
  follow rootCursor word = some edge

theorem follow_extend {start target : Cursor} {word : List Bool}
    (path : follow start word = some (.branch target)) (b : Bool) :
    follow start (word ++ [b]) = outgoing target b := by
  induction word generalizing start with
  | nil =>
    simp only [follow, Option.some.injEq, Edge.branch.injEq] at path
    subst target
    simp only [List.nil_append, follow]
    cases outgoing start b with
    | none => rfl
    | some e => cases e <;> rfl
  | cons c word ih =>
    cases hr : outgoing start c with
    | none => simp [follow, hr] at path
    | some e =>
      cases e with
      | branch next =>
        simp only [follow, hr] at path
        simp only [List.cons_append, follow, hr]
        exact ih path
      | instruction op =>
        cases word <;> simp [follow, hr] at path

theorem AtEdge.step {word : List Bool} {cur : Cursor} {edge : Edge}
    (path : AtEdge word (.branch cur)) {bit : Bool} (move : outgoing cur bit = some edge) :
    AtEdge (word ++ [bit]) edge :=
  (follow_extend path bit).trans move

end I0451.Runtime
