module
public import I3_334Support.Calibration.TruthDecoding
public import I3_334Support.Arithmetic.SetValuedRecursion
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V}

structure TruthData (V : Type) where
  omega : V
  domain : V
  atoms : V
  fallback : V

abbrev arith {n : Nat} (φ : Semiformula ℒₒᵣ Empty n) (omega : V) (args : Fin n → V) : Prop :=
  arithmeticOn (E := E) (G := G) φ omega args

def AtomLayer (negative : Bool) (d : TruthData V) (p env : V) : Prop :=
  ∃ atom, arith (E := E) (G := G) (atomInputDef (if negative then 1 else 0)).val d.omega
      ![atom,p,env,d.fallback] ∧
    (if negative then ¬E atom d.atoms else E atom d.atoms)

def BinaryLayer (conjunctive : Bool) (N : SetContext (ClassRelation.algebra E G) V)
    (d : TruthData V) (p prior env : V) : Prop :=
  ∃ a b, arith (E := E) (G := G) (binaryInputDef (if conjunctive then 4 else 5)).val d.omega ![p,a,b] ∧
    if conjunctive then N.FamilyTruth prior a env ∧ N.FamilyTruth prior b env
    else N.FamilyTruth prior a env ∨ N.FamilyTruth prior b env

def BinderLayer (universal : Bool) (N : SetContext (ClassRelation.algebra E G) V)
    (d : TruthData V) (p prior env : V) : Prop :=
  ∃ a, arith (E := E) (G := G) (unaryInputDef (if universal then 6 else 7)).val d.omega ![p,a] ∧
    let body := fun x => ∃ updated, arith (E := E) (G := G) pushInputDef.val d.omega ![updated,x,env] ∧
      N.FamilyTruth prior a updated
    if universal then ∀ x, E x d.domain → body x else ∃ x, E x d.domain ∧ body x

def FormulaLayer (N : SetContext (ClassRelation.algebra E G) V)
    (d : TruthData V) (p prior env : V) : Prop :=
  arith (E := E) (G := G) truthInputDef.val d.omega ![p] ∨
    AtomLayer (E := E) (G := G) false d p env ∨ AtomLayer (E := E) (G := G) true d p env ∨
    BinaryLayer true N d p prior env ∨ BinaryLayer false N d p prior env ∨
    BinderLayer true N d p prior env ∨ BinderLayer false N d p prior env

set_option maxHeartbeats 65000 in
theorem atomLayer_formula (laws : ClassAxioms E G) (inhabited : Nonempty V) {n w t u i e : Nat}
    (hw : w<n) (ht : t<n) (hu : u<n) (hi : i<n) (he : e<n)
    (negative : Bool) :
    (laws.context inhabited).square.Definable n (fun v => AtomLayer (E := E) (G := G) negative ⟨v w,v w,v t,v u⟩ (v i) (v e)) := by
  let N := laws.context inhabited
  have decode := arithmeticOn_definable (E := E) (G := G) (atomInputDef (if negative then 1 else 0)).val
    (scope := n+1) (omega := w+1) (arg := ![0,i+1,e+1,u+1]) (by omega)
    (by intro j; fin_cases j <;> simp <;> omega)
  have member := Definable.mem (N := N) (n := n+1) (i := 0) (j := t+1) (by omega) (by omega)
  have decoded : N.square.Definable (n+1) _ := decode
  have mem : N.square.Definable (n+1) (fun v => E (v 0) (v (t+1))) :=
    member
  have decode' : N.square.Definable (n+1) (fun v => arith (E := E) (G := G)
      (atomInputDef (if negative then 1 else 0)).val (v (w+1)) ![v 0,v (i+1),v (e+1),v (u+1)]) :=
    decoded.congr (fun v => by
      have values : (fun j => v ((![0,i+1,e+1,u+1] : Fin 4 → Nat) j)) =
          ![v 0,v (i+1),v (e+1),v (u+1)] := by funext j; fin_cases j <;> rfl
      rw [values])
  cases negative
  · have answer := Definable.ex (n := n) (decode'.and mem)
    refine answer.congr (fun _ => ?_)
    exact Iff.rfl
  · have answer := Definable.ex (n := n) (decode'.and mem.not)
    refine answer.congr (fun _ => ?_)
    exact Iff.rfl


end PalomarI3380.Calibration.CodedGraph
