module
public import GateValuations
public import LiteralGate
@[expose] public section
namespace C207Soundness
universe u
variable {α : Type u}
def pointedGateCode (a d h : Nat) : Nat :=
  (impCode (impCode (impCode (eqCode h d) (allCode a (eqCode h d))) (impCode (impCode (memCode h d) (allCode a (memCode h d))) (allCode a (impCode (allCode h (impCode (memCode h a) (impCode (allCode d (impCode a (impCode (allCode d (impCode (allCode a (impCode (memCode a d) (memCode a h))) (allCode h (impCode a (impCode (allCode h (impCode a (impCode (memCode h a) 1))) 1))))) 1))) 1))) (impCode (impCode a (memCode h a)) 1))))) 1)

end C207Soundness
