module

public import PA215PA.PAInterpretedClosedSource
public import PA215PA.PAForwardRelationalClosureSupport

@[expose] public section

/-! Exact closure conversion with all finite-support obligations discharged.
The sole proof premise is the already fully closed guarded target theorem. -/
namespace PA215.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Converts one fully closed guarded target proof to the interpretation of the
actual source univCl'. All initial indices below fvSup are quantified, including
unused gaps; only the listed guard indices require the displayed bound. -/
def closedGuardToSourceUniversalClosure {Γ : List Form}
    (p : SourceFormula 0) (is : List Nat)
    (his : ∀ i, i ∈ is → i < p.fvSup)
    (h : ND.Proof Γ (closeParameters p.fvSup
      (inductionParameterGuard is (fun i => &i) 🡒 formula p Fin.elim0 (fun i => &i))))
    (f : Nat → Term 0) : ND.Proof Γ (formula p.univCl' Fin.elim0 f) :=
  closedGuardToSourceUniversalClosureOfSupport p is his
    (canonical_formula_support_bound p) h f

#print axioms closedGuardToSourceUniversalClosure
end PA215.PA.ForwardRelational
