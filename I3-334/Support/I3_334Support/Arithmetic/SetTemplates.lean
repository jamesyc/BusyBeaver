module
public import I3_334Support.Logic.ExpandedTemplates
public import I3_334Support.Logic.SetScope
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type} {E G : V → V → Prop}

def numeralAt (n : Nat) (a : Argument V) : Formula V :=
  applyTemplate (SetFormula.numeral n 0) 1 (fun _ => a)

theorem numeralAt_scope {n k : Nat} {a : Argument V} (ha : a.bound k) : Bound (numeralAt n a) k :=
  applyTemplate_scope _ (SetFormula.scope_numeral n (Nat.zero_lt_succ 0)) _ (fun _ _ => ha)

theorem numeralAt_eval (n : Nat) (a : Argument V) (env : Nat → V) :
    eval E G (numeralAt n a) env ↔ Internal.Numeral E n (a.value env) :=
  (applyTemplate_eval _ (SetFormula.scope_numeral n (Nat.zero_lt_succ 0)) _ env).trans
    (SetFormula.holds_numeral n (Nat.zero_lt_succ 0))

def threeArgs (a b c : Argument V) : Nat → Argument V
  | 0 => a
  | 1 => b
  | _ => c

theorem threeArgs_scope {n : Nat} {a b c : Argument V}
    (ha : a.bound n) (hb : b.bound n) (hc : c.bound n) : ∀ i, (threeArgs a b c i).bound n
  | 0 => ha
  | 1 => hb
  | _+2 => hc

def additionAt (a b c : Argument V) : Formula V :=
  applyTemplate (SetFormula.addition 0 1 2) 3 (threeArgs a b c)

theorem additionAt_scope {n : Nat} {a b c : Argument V}
    (ha : a.bound n) (hb : b.bound n) (hc : c.bound n) : Bound (additionAt a b c) n :=
  applyTemplate_scope _ (SetFormula.scope_addition (by decide) (by decide) (by decide)) _
    (fun i _ => threeArgs_scope ha hb hc i)

theorem additionAt_eval (a b c : Argument V) (env : Nat → V) :
    eval E G (additionAt a b c) env ↔ Internal.Add E (a.value env) (b.value env) (c.value env) :=
  (applyTemplate_eval _ (SetFormula.scope_addition (by decide) (by decide) (by decide)) _ env).trans
    (SetFormula.holds_addition (by decide) (by decide) (by decide))

def multiplicationAt (a b c : Argument V) : Formula V :=
  applyTemplate (SetFormula.multiplication 0 1 2) 3 (threeArgs a b c)

theorem multiplicationAt_scope {n : Nat} {a b c : Argument V}
    (ha : a.bound n) (hb : b.bound n) (hc : c.bound n) : Bound (multiplicationAt a b c) n :=
  applyTemplate_scope _ (SetFormula.scope_multiplication (by decide) (by decide) (by decide)) _
    (fun i _ => threeArgs_scope ha hb hc i)

theorem multiplicationAt_eval (a b c : Argument V) (env : Nat → V) :
    eval E G (multiplicationAt a b c) env ↔ Internal.Mul E (a.value env) (b.value env) (c.value env) :=
  (applyTemplate_eval _ (SetFormula.scope_multiplication (by decide) (by decide) (by decide)) _ env).trans
    (SetFormula.holds_multiplication (by decide) (by decide) (by decide))

end PalomarI3380.Logic.Expanded
