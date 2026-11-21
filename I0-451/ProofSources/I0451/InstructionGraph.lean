module
public import I0451.LiteralExecution

/-! Structured control for the register program. Its edges are extracted
from the literal decoder; it uses the two bits already read as part of
the decoder control. The semantics describes an entire subtree at a
time, including carried break and restart signals. -/
@[expose] public section
namespace I0451.Runtime

structure Cursor where
  control : Nat
  previous : Bool
  earlier : Bool
  deriving DecidableEq, Repr

inductive Instruction where
  | inc (r : Fin 9)
  | dec (r : Fin 9)
  | break (depth : Nat)
  | restart (depth : Nat)
  | halt
  deriving DecidableEq, Repr

inductive Edge where
  | branch (cursor : Cursor)
  | instruction (op : Instruction)
  deriving DecidableEq, Repr

/-- Translate a decoder leaf to the corresponding register-level
operation. A break or restart stores its positive depth minus one. -/
def instruction : Decoder.Exit → Option Instruction
  | .issue q =>
    if q = 451 then some .halt
    else
      match registerAddress q with
      | none => none
      | some (op, i) =>
        if bounded : i < 9 then
          some (match op with | .inc => .inc ⟨i, bounded⟩ | .dec => .dec ⟨i, bounded⟩)
        else none
  | .erase q =>
    if q = breakOne then some (.break 0)
    else if q = continueZero then some (.restart 0)
    else if q = continueOne then some (.restart 1)
    else none
  | .fused => some (.restart 2)

def outgoing (cursor : Cursor) (read : Bool) : Option Edge :=
  match Decoder.arm cursor.control cursor.previous cursor.earlier read with
  | none => none
  | some (.inl next) => some (.branch ⟨next, read, cursor.previous⟩)
  | some (.inr exit) => (instruction exit).map Edge.instruction

def rootCursor : Cursor := ⟨root, true, false⟩

def mainEdge : Edge := .branch rootCursor

abbrev Registers := Fin 9 → Nat

def putRegister {α : Type} (regs : Fin 9 → α) (index : Fin 9) (value : α) : Fin 9 → α :=
  fun j => if j = index then value else regs j

@[simp] theorem putRegister_at {α : Type} (regs : Fin 9 → α) (i : Fin 9) (value : α) :
    putRegister regs i value i = value := by
  simp [putRegister]

theorem putRegister_other {α : Type} (regs : Fin 9 → α) {i j : Fin 9} (ne : j ≠ i) (value : α) :
    putRegister regs i value j = regs j := by
  simp [putRegister, ne]

inductive Signal where
  | normal
  | break (depth : Nat)
  | restart (depth : Nat)
  | halt
  deriving DecidableEq, Repr

/-- On the left side, the first break skips the remainder of the
current sequence. A normal completion enters the right side. -/
def Signal.leftExit : Signal → Option Signal
  | .normal => none
  | .break 0 => some .normal
  | .break (n + 1) => some (.break n)
  | .restart n => some (.restart n)
  | .halt => some .halt

/-- On the right side, the first restart reenters the current sequence. -/
def Signal.rightExit : Signal → Option Signal
  | .restart 0 => none
  | .restart (n + 1) => some (.restart n)
  | other => some other

/-- Finite execution of a structured register subtree. The branch rules
are justified directly by the interpreter's address operations. -/
inductive Executes : Edge → Registers → Signal → Registers → Prop where
  | inc (index : Fin 9) (regs : Registers) :
      Executes (.instruction (.inc index)) regs .normal
        (putRegister regs index (regs index + 1))
  | decPositive (index : Fin 9) (regs : Registers) (value : Nat)
      (positive : regs index = value + 1) :
      Executes (.instruction (.dec index)) regs .normal (putRegister regs index value)
  | decZero (index : Fin 9) (regs : Registers) (zero : regs index = 0) :
      Executes (.instruction (.dec index)) regs (.break 0) regs
  | break (depth : Nat) (regs : Registers) :
      Executes (.instruction (.break depth)) regs (.break depth) regs
  | restart (depth : Nat) (regs : Registers) :
      Executes (.instruction (.restart depth)) regs (.restart depth) regs
  | halt (regs : Registers) : Executes (.instruction .halt) regs .halt regs
  | leftExit {cursor : Cursor} {left : Edge} {first last : Registers} {inner result : Signal}
      (fromLeft : outgoing cursor false = some left)
      (runLeft : Executes left first inner last) (signal : inner.leftExit = some result) :
      Executes (.branch cursor) first result last
  | rightExit {cursor : Cursor} {left right : Edge} {first middle last : Registers}
      {inner result : Signal}
      (fromLeft : outgoing cursor false = some left)
      (fromRight : outgoing cursor true = some right)
      (runLeft : Executes left first .normal middle)
      (runRight : Executes right middle inner last) (signal : inner.rightExit = some result) :
      Executes (.branch cursor) first result last
  | repeat {cursor : Cursor} {left right : Edge} {first middle restart last : Registers}
      {result : Signal}
      (fromLeft : outgoing cursor false = some left)
      (fromRight : outgoing cursor true = some right)
      (runLeft : Executes left first .normal middle)
      (runRight : Executes right middle (.restart 0) restart)
      (runAgain : Executes (.branch cursor) restart result last) :
      Executes (.branch cursor) first result last

end I0451.Runtime
