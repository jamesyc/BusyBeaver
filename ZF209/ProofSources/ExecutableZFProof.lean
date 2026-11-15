module
public import ExecutableNDChecker
public import ExecutableZFAxioms
@[expose] public section
namespace ZFR.ExecutableZF
abbrev ValidContext (Γ : Context) := ∀ a, a ∈ Γ → sourceZfrAxiom (encodeFormula a)
abbrev CheckedContext := { Γ : Context // ValidContext Γ }

def checkContext : List AxiomWitness → Option CheckedContext
 | [] => some ⟨[], by intro a ha; cases ha⟩
 | w :: rest => do
   let ⟨a, ha⟩ ← checkAxiom w
   let ⟨Γ, hΓ⟩ ← checkContext rest
   pure ⟨a :: Γ, by
     intro b hb
     rcases List.mem_cons.mp hb with he | hb
     · exact he ▸ ha
     · exact hΓ b hb⟩

abbrev CheckedTheorem := { a : Formula // sourceTheoryProvable sourceZfrAxiom (encodeFormula a) }

/-- Executable full proof checker relative to the exact pre-existing ZFR theory.
Axiom witnesses accompany a finite natural-deduction certificate; all context,
inference, variable-scope and schema checks are executable, not axioms. -/
def checkTheorem (axioms : List AxiomWitness) (certificate : Executable.Cert) :
    Option CheckedTheorem := do
 let ⟨Γ, hΓ⟩ ← checkContext axioms
 let ⟨row, hrow⟩ ← Executable.check certificate
 match hr : row with
 | .branches _ _ _ _ => none
 | .seq Δ a =>
   if hc : Δ = Γ then
     if hclosed : boundCheck a 0 = true then
       pure ⟨a, (hr ▸ hrow).theoryProvable (by simpa [hc] using hΓ)⟩
     else none
   else none

def conclusion (axioms : List AxiomWitness) (certificate : Executable.Cert) : Option Formula :=
 (checkTheorem axioms certificate).map Subtype.val

end ZFR.ExecutableZF
