module
public import SourceSyntax
public import Foundation.FirstOrder.SetTheory.Basic.Misc
@[expose] public section
namespace ZFR.FoundationBridge
open FFL.FirstOrder

def termIndex {n : Nat} : Semiterm Language.set Nat n → Nat
 | .bvar i => i.val
 | .fvar j => n+j
 | .func f _ => nomatch f

def atom {n k : Nat} (r : Language.Set.Rel k)
 (v : Fin k → Semiterm Language.set Nat n) : ZFR.Formula :=
 match r with
 | .eq => .eq (termIndex (v 0)) (termIndex (v 1))
 | .mem => .mem (termIndex (v 0)) (termIndex (v 1))

/-- Actual pinned Foundation syntax, not a mirrored substitute. Bound variables
keep their indices; free variables are shifted above the bound-variable block. -/
def toSource {n : Nat} : Semiformula Language.set Nat n → ZFR.Formula
 | .verum => .imp .bot .bot
 | .falsum => .bot
 | .rel r v => atom r v
 | .nrel r v => .imp (atom r v) .bot
 | .and p q => .and (toSource p) (toSource q)
 | .or p q => .or (toSource p) (toSource q)
 | .all p => .all (toSource p)
 | .exs p => .ex (toSource p)

end ZFR.FoundationBridge
