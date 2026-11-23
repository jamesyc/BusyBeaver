module
public import I3_334Support.Logic.I3
public import I3_334Support.Logic.History
@[expose] public section

namespace PalomarI3380.Logic

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
def ArithTerm.value {V : Type} [Zero V] [One V] [Add V] [Mul V] :
    ArithTerm → (Nat → V) → V
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.value s+q.value s
 | .mul p q,s=>p.value s*q.value s

def SigmaFormula.value {V : Type} [Zero V] [One V] [Add V] [Mul V] [LT V] :
    SigmaFormula → (Nat → V) → Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.value s=q.value s else p.value s<q.value s
   if pos then P else ¬P
 | .conj p q,s=>p.value s ∧ q.value s
 | .disj p q,s=>p.value s ∨ q.value s
 | .exists_ p,s=>∃x,p.value (pushValue s x)
 | .forallLt b p,s=>∀x,x<b.value s→p.value (pushValue s x)

abbrev ArithTerm.natValue (t : ArithTerm) (s : Nat → Nat) : Nat := t.value s
abbrev SigmaFormula.natEval (φ : SigmaFormula) (s : Nat → Nat) : Prop := φ.value s

open Internal
/-- Fully relational evaluation, including arithmetic internal to a set model. -/
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
/-- Correct arithmetic meaning in every ZFC + I3 model, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→ZFCI3Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- Arithmetic Σ₁-soundness of ZFC + I3 under the standard interpretation in its natural numbers. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 ZFCI3Provable ψ→∀s:Nat→Nat,φ.natEval s

end PalomarI3380.Logic
