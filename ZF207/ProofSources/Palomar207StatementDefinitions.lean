module
public import Palomar207HistoryDefinition
public import Palomar207ZFDefinition
@[expose] public section
/-! Modular DESIGN source only. A final Challenge must amalgamate these
transparent definitions into one Std-only file; these local imports are not
claimed to meet Challenge import rules. No theorem or bridge is assumed. -/
namespace PalomarZF207
inductive ArithTerm where
 | zero | one
 | var (index:Nat)
 | add (left right:ArithTerm)
 | mul (left right:ArithTerm)
inductive SigmaFormula where
 | atom (left right:ArithTerm) (equality positive:Bool)
 | conj (left right:SigmaFormula)
 | disj (left right:SigmaFormula)
 | exists_ (body:SigmaFormula)
 | forallLt (bound:ArithTerm) (body:SigmaFormula)
def ArithTerm.bound : ArithTerm→Nat→Prop
 | .zero,_ | .one,_=>True
 | .var i,n=>i<n
 | .add p q,n | .mul p q,n=>p.bound n ∧ q.bound n
def SigmaFormula.bound : SigmaFormula→Nat→Prop
 | .atom p q _ _,n=>p.bound n ∧ q.bound n
 | .conj p q,n | .disj p q,n=>p.bound n ∧ q.bound n
 | .exists_ p,n=>p.bound (n+1)
 | .forallLt t p,n=>t.bound n ∧ p.bound (n+1)
def ArithTerm.natValue : ArithTerm→(Nat→Nat)→Nat
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.natValue s+q.natValue s
 | .mul p q,s=>p.natValue s*q.natValue s
def SigmaFormula.natEval : SigmaFormula→(Nat→Nat)→Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.natValue s=q.natValue s else p.natValue s<q.natValue s
   if pos then P else ¬P
 | .conj p q,s=>p.natEval s ∧ q.natEval s
 | .disj p q,s=>p.natEval s ∨ q.natEval s
 | .exists_ p,s=>∃x:Nat,p.natEval (pushValue s x)
 | .forallLt b p,s=>∀x:Nat,x<b.natValue s→p.natEval (pushValue s x)
open PalomarZF207History
/-- Fully relational evaluation, including arithmetic internal to a ZF model. -/
def ArithTerm.graph {V:Type} (E:V→V→Prop):ArithTerm→(Nat→V)→V→Prop
 | .zero,_,z=>Numeral E 0 z
 | .one,_,z=>Numeral E 1 z
 | .var i,s,z=>NatObject E z ∧ z=s i
 | .add p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Add E a b z
 | .mul p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Mul E a b z
def SigmaFormula.internalEval {V:Type} (E:V→V→Prop):SigmaFormula→(Nat→V)→Prop
 | .atom p q eq pos,s=>∃a b,p.graph E s a ∧ q.graph E s b ∧
   (if pos then (if eq then a=b else E a b) else ¬(if eq then a=b else E a b))
 | .conj p q,s=>p.internalEval E s ∧ q.internalEval E s
 | .disj p q,s=>p.internalEval E s ∨ q.internalEval E s
 | .exists_ p,s=>∃x:V,NatObject E x ∧ p.internalEval E (pushValue s x)
 | .forallLt b p,s=>∃bound,b.graph E s bound ∧
   ∀x:V,NatObject E x→E x bound→p.internalEval E (pushValue s x)
/-- Correct arithmetic meaning in ALL ZF models, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- The full Sigma1 class, independent of the chosen halting sentence. Its
 equivalence to the production hypothesis is an outstanding Solution theorem. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 Provable ψ→∀s:Nat→Nat,φ.natEval s
/-- Uniform meaning is intended as a CONCLUSION of the compared theorem,
not as a premise that lets a caller supply an unspecified machine predicate. -/
def Represents207 (H:Formula):Prop:=
 Closed H ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→Model E→
 ∀s:Nat→V,eval E H s ↔ InternalLinkedHalts E
/-- Proposed full statement of record. This is a transparent proposition, not
an axiom or a theorem claiming the new Challenge interface is already proved. -/
def Exact207Claim:Prop:=∃H:Formula,Represents207 H ∧
 (Consistent→¬Provable (Neg H)) ∧
 (ArithmeticSigma1Sound→(¬Provable H) ∧ (¬Provable (Neg H)))
end PalomarZF207
