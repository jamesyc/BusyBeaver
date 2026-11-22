module
public import ZF192Support.Execution.Registers.Commands.AX.Scan
public import ZF192Support.Calculus.Generic.Logic
@[expose] public section
set_option maxRecDepth 20000
namespace ZF192Support.NativeAXSymbolic
inductive Expr where
  | zero | atom (i : Fin 6) | succ (x : Expr) | add (x y : Expr) | im (x y : Expr)
  deriving DecidableEq, Repr

def plus : Expr → Expr → Expr
  | .zero, y => y
  | x, .zero => x
  | x, y => .add x y

structure Store where
  t : Expr
  a : Expr
  d : Expr
  h : Expr
  fields : List Expr
  stack : List Expr
  deriving DecidableEq, Repr

def exec : Op → Store → Option Store
  | .push, s => some {s with t := .zero, stack := s.t :: s.stack}
  | .cons, s => match s.stack with
    | [] => none
    | v :: vs => some {s with t := .im v s.t, stack := vs}
  | .copyA, s => some {s with t := plus s.t s.a}
  | .copyD, s => some {s with t := plus s.t s.d}
  | .copyH, s => some {s with t := plus s.t s.h}
  | .incT, s => some {s with t := .succ s.t}
  | .readH, s => match s.fields with
    | [] => none
    | v :: vs => some {s with h := plus s.h v, fields := vs}
  | .readD, s => match s.fields with
    | [] => none
    | v :: vs => some {s with d := plus s.d v, fields := vs}

def run : List Op → Store → Option Store
  | [], s => some s
  | op :: ops, s => (exec op s).bind (run ops)

def initial : Store := ⟨.atom 0,.atom 1,.atom 2,.atom 3,[.atom 4,.atom 5],[]⟩
def symbolicCodes : CKernel.Generic.Codes Expr where
  imp := .im
  mem := fun x y => .succ (.im x y)
  eq := fun x y => .succ (.succ (.succ (.im x y)))
  all := fun x y => .succ (.succ (.im y x))
  bot := .succ .zero

/-- AX loads the new labels, pushes its axiom heads and leaves the gate in the accumulator. -/
def actualResult : Store :=
  let t := Expr.atom 0
  let a := Expr.atom 1
  let oldD := Expr.atom 2
  let oldH := Expr.atom 3
  let d := Expr.add oldD (.atom 5)
  let h := Expr.add oldH (.atom 4)
  ⟨symbolicCodes.bundle h d a, a, d, h, [],
   symbolicCodes.axHeads a d h oldD oldH ++ [t]⟩

end ZF192Support.NativeAXSymbolic
