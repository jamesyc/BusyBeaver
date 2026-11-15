module
public import SearchCommands
@[expose] public section
namespace C209Search.AXMacro
open C209Soundness M6.Source.Cantor

def stackCode (xs : List Nat) (tail : Nat) : Nat := xs.foldr pair tail
inductive Op where
  | push | cons | copyA | copyD | copyH | incT | readH | readD
  deriving DecidableEq, Repr

structure Store where
  t : Nat
  a : Nat
  d : Nat
  h : Nat
  l : Nat
  stack : List Nat
  deriving DecidableEq, Repr

def exec : Op → Store → Option Store
  | .push, s => some {s with t := 0, stack := s.t :: s.stack}
  | .cons, s => match s.stack with
    | [] => none
    | v :: vs => some {s with t := impCode v s.t, stack := vs}
  | .copyA, s => some {s with t := s.t+s.a}
  | .copyD, s => some {s with t := s.t+s.d}
  | .copyH, s => some {s with t := s.t+s.h}
  | .incT, s => some {s with t := s.t+1}
  | .readH, s => some {s with h := s.h+(M6.Source.Cantor.decode s.l).1, l := (M6.Source.Cantor.decode s.l).2}
  | .readD, s => some {s with d := s.d+(M6.Source.Cantor.decode s.l).1, l := (M6.Source.Cantor.decode s.l).2}

def run : List Op → Store → Option Store
  | [], s => some s
  | op :: ops, s => (exec op s).bind (run ops)


def program : List Op := [.push,.copyH,.push,.copyD,.cons,.incT,.incT,.readH,.push,.copyH,.push,.copyD,.cons,.readD,.push,.copyD,.cons,.push,.copyD,.push,.copyH,.cons,.push,.copyA,.push,.copyH,.cons,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyH,.cons,.push,.copyH,.push,.copyA,.cons,.incT,.incT,.push,.copyD,.cons,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyH,.push,.copyA,.cons,.incT,.incT,.incT,.push,.copyA,.push,.copyD,.cons,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyA,.push,.copyH,.cons,.incT,.push,.copyA,.push,.copyD,.cons,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.push,.copyA,.push,.copyD,.cons,.incT,.incT,.push,.copyA,.push,.copyH,.cons,.push,.copyD,.cons,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.cons,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.incT,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyH,.push,.copyD,.cons,.incT,.push,.copyA,.cons,.incT,.incT,.cons,.push,.copyH,.push,.copyA,.cons,.incT,.push,.copyA,.push,.copyA,.push,.copyD,.cons,.incT,.push,.copyA,.push,.copyH,.cons,.incT,.cons,.push,.copyA,.cons,.incT,.incT,.push,.copyA,.push,.copyA,.push,.copyH,.push,.copyA,.cons,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyD,.cons,.incT,.incT,.push,.incT,.cons,.cons,.push,.copyH,.cons,.incT,.incT,.push,.copyA,.push,.copyH,.push,.copyA,.cons,.incT,.cons,.push,.incT,.cons,.cons,.push,.copyA,.cons,.incT,.incT,.cons,.cons,.push,.incT,.cons]
end C209Search.AXMacro
