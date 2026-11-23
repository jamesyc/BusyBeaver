module
public import I3_334Support.Calibration.MembershipTemplates
public import I3_334Support.Calibration.RelationalTheory
public import I3_334Support.Calibration.ArithmeticInterpretation.StandardSemantics
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder
open Logic (SetFormula)
open ArithmeticInterpretation (Interp)

def naturalName : Semisentence FilterLanguage 1 :=
  namedMembership 1 (SetFormula.natObject 0 1)

def numeralName (value : Nat) : Semisentence FilterLanguage 1 :=
  namedMembership 1 (SetFormula.numeral value 0 1)

def sameName : Semisentence FilterLanguage 2 :=
  namedMembership 2 (.eq 0 1)

/-- Read a named natural number as itself, with zero as the value of
every other algebra element. The output is always a named natural. -/
def readsName : Semisentence FilterLanguage 2 :=
  (naturalName ⇜ ![.bvar 1]) ⋏
  (((naturalName ⇜ ![.bvar 0]) ⋏ sameName) ⋎
    (∼(naturalName ⇜ ![.bvar 0]) ⋏ (numeralName 0 ⇜ ![.bvar 1])))

def arithmeticTemplate (arity : Nat) (p : SetFormula) : Semisentence FilterLanguage arity :=
  ∃¹^[arity] (Matrix.conj (fun i : Fin arity =>
    readsName ⇜ ![.bvar (i.addNat arity),.bvar (i.addCast arity)]) ⋏
    (namedMembership arity (p arity) ⇜ fun i => .bvar (i.addCast arity)))

def markedTemplate (arity : Nat) (p : SetFormula) : Semisentence GraphLanguage (arity+1) :=
  graphFormula (Rew.bShift ▹ arithmeticTemplate arity p)

/-- The filter algebra interprets arithmetic through its named point
quotient. The extra marker is a dummy parameter for the proof transport. -/
def filterInterpretation : Interp where
  mark := ⊤
  dom := ⊤
  eq := markedTemplate 2 (SetFormula.eq 1 0)
  lt := markedTemplate 2 (SetFormula.mem 1 0)
  zero := markedTemplate 1 (SetFormula.numeral 0 0)
  one := markedTemplate 1 (SetFormula.numeral 1 0)
  add := markedTemplate 3 (SetFormula.addition 2 1 0)
  mul := markedTemplate 3 (SetFormula.multiplication 2 1 0)

end PalomarI3380.Calibration
