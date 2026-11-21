module
public import Std

/-! A binary, two-way-infinite tape. Each side of the head is a stack of
bits encoded little-endian. The omitted high bits of either stack are all
zero. The left stack starts immediately to the left of the head, and the
right stack starts at the head. -/

@[expose] public section
namespace I0451

/-- Rows are base-2048 digits, ordered by state and read bit starting
with the least significant digit. Zero means no row. A move is a digit
`1 + 4*q + 2*d + b`, writing bit `b` and entering state `q`.
Direction `d = 1` moves right. -/
abbrev Table := Nat

structure Config where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def bit (n : Nat) : Bool := n % 2 == 1

def push (b : Bool) (tail : Nat) : Nat := b.toNat + 2 * tail

def digit (table : Table) (index : Nat) : Nat :=
  table / 2048 ^ index % 2048

def row (table : Table) (q : Nat) (read : Bool) : Nat :=
  digit table (2 * q + read.toNat)

/-- Apply a known transition code to the current tape. -/
def move (code : Nat) (left right : Nat) : Config :=
  if bit (code / 2) then
    ⟨code / 4, push (bit code) left, right / 2⟩
  else
    ⟨code / 4, left / 2, push (bit left) (push (bit code) (right / 2))⟩

def step (table : Table) (c : Config) : Option Config :=
  match row table c.state (bit c.right) with
  | 0 => none
  | code + 1 => some (move code c.left c.right)

def run (table : Table) : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step table c).bind (run table k)

def blank (state : Nat) : Config := ⟨state, 0, 0⟩

/-- A run halts when it reaches the first configuration with no next move. -/
def Halts (table : Table) (initial : Config) : Prop :=
  ∃ n c, run table n initial = some c ∧ step table c = none

end I0451
