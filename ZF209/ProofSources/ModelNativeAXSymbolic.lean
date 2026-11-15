module
public import ModelNativeAXOps
@[expose] public section
set_option maxRecDepth 20000
namespace ZF209.NativeAXSymbolic
inductive Op where
  | push | cons | copyA | copyD | copyH | incT | readH | readD
  deriving DecidableEq, Repr

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

def program : List Op := [.push,.copyH,.push,.copyD,.cons,.incT,.incT,.readH,.push,.copyH,.push,.copyD,.cons,.readD,.push,.copyD,.cons,.push,.copyD,.push,.copyH,.cons,.push,.copyA,.push,.copyH,.cons,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyH,.cons,.push,.copyH,.push,.copyA,.cons,.incT,.incT,.push,.copyD,.cons,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyH,.push,.copyA,.cons,.incT,.incT,.incT,.push,.copyA,.push,.copyD,.cons,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyA,.push,.copyH,.cons,.incT,.push,.copyA,.push,.copyD,.cons,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyA,.push,.copyD,.cons,.incT,.incT,.push,.copyA,.push,.copyH,.cons,.push,.copyD,.cons,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyA,.cons,.incT,.push,.copyA,.push,.copyA,.push,.copyD,.cons,.incT,.push,.copyA,.push,.copyH,.cons,.incT,.cons,.push,.copyA,.cons,.incT,.incT,.push,.copyA,.push,.copyA,.push,.copyH,.push,.copyA,.cons,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.push,.copyA,.push,.copyH,.push,.copyA,.cons,.incT,.cons,.push,.incT,.cons,.cons,.push,.copyA,.cons,.incT,.incT,.cons,.cons,.push,.incT,.cons]
def initial : Store := ⟨.atom 0,.atom 1,.atom 2,.atom 3,[.atom 4,.atom 5],[]⟩
def actualResult : Store := ⟨(.im (.im (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.succ (.succ (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.atom 1))))) (.im (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.succ (.succ (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.atom 1))))) (.succ (.succ (.im (.im (.succ (.succ (.im (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1))) (.im (.succ (.succ (.im (.im (.atom 1) (.im (.succ (.succ (.im (.im (.succ (.succ (.im (.im (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))) (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4))))) (.atom 1)))) (.succ (.succ (.im (.im (.atom 1) (.im (.succ (.succ (.im (.im (.atom 1) (.im (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1))) (.succ .zero))) (.add (.atom 3) (.atom 4))))) (.succ .zero))) (.add (.atom 3) (.atom 4)))))) (.add (.atom 2) (.atom 5))))) (.succ .zero))) (.add (.atom 2) (.atom 5))))) (.succ .zero))) (.add (.atom 3) (.atom 4))))) (.im (.im (.atom 1) (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1)))) (.succ .zero))) (.atom 1)))))) (.succ .zero)),(.atom 1),(.add (.atom 2) (.atom 5)),(.add (.atom 3) (.atom 4)),[],[(.im (.succ (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5))))) (.im (.succ (.succ (.im (.im (.atom 1) (.add (.atom 3) (.atom 4))) (.add (.atom 2) (.atom 5))))) (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))))),(.im (.succ (.succ (.im (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.succ .zero)) (.add (.atom 2) (.atom 5))))) (.succ .zero)),(.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))))) (.im (.succ (.im (.atom 1) (.add (.atom 3) (.atom 4)))) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))),(.im (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5)))) (.im (.succ (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1))))) (.succ (.im (.atom 1) (.add (.atom 2) (.atom 5)))))),(.im (.succ (.succ (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.atom 1)))) (.add (.atom 2) (.atom 5))))) (.succ (.succ (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))) (.atom 1))))),(.im (.im (.succ (.succ (.im (.im (.succ (.succ (.im (.add (.atom 3) (.atom 4)) (.add (.atom 2) (.atom 5))))) (.succ .zero)) (.add (.atom 2) (.atom 5))))) (.succ .zero)) (.add (.atom 3) (.atom 4))),(.im (.im (.im (.add (.atom 3) (.atom 4)) (.atom 2)) (.add (.atom 2) (.atom 5))) (.im (.im (.add (.atom 2) (.atom 5)) (.add (.atom 3) (.atom 4))) (.im (.atom 1) (.add (.atom 3) (.atom 4))))),(.succ (.succ (.im (.atom 3) (.atom 2)))),(.atom 0)]⟩
theorem program_actual : run program initial = some actualResult := by decide +kernel

end ZF209.NativeAXSymbolic
