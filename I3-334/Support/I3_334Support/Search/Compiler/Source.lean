module
public import I3_334Support.Search.Compiler.Program
@[expose] public section

namespace PalomarI3380.Compiler.Source

def inc (r : Register) : Program := .op (.inc r)
def dec (r : Register) : Program := .op (.decNZ r)
def break_ (n : Nat) : Program := .op (.break_ n)
def continue_ (extra : Nat) : Program := .op (.continue_ extra)
def halt : Program := .op .halt

/-- Sequences in the source builder associate to the right, with an empty
list used as an identity. -/
def block : List Program → Program
  | [] => break_ 0
  | [p] => p
  | p :: q :: ps => .seq p (block (q :: ps))

def whilePositive (r : Register) (body : Program) : Program :=
  .seq (dec r) (.seq body (continue_ 1))

def clear (r : Register) : Program := .seq (dec r) (continue_ 0)

def ifPositive (r : Register) (body : Program) : Program := .seq (dec r) body

def ifZero (r : Register) (body : Program) : Program :=
  .seq (.seq (dec r) (break_ 1)) body

def move (src dst : Register) : Program := whilePositive src (inc dst)

def unpair (first second src : Register) : Program :=
  whilePositive src (.seq (inc second) (ifZero first (move second first)))

end PalomarI3380.Compiler.Source
