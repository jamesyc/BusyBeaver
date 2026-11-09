module

public import PA215PA.RelationalPredicateTemplateLiftLanguage

@[expose] public section
namespace PA215.PA.RelationalPredicateTemplate.ND
open FFL FFL.FirstOrder

def up {Γ : List Form} {p : Form} (d : Proof Γ p) (q : Form) : Proof (q::Γ) p :=
  weaken d (by intro x hx; simp [hx])

def shiftProof {Γ : List Form} {p : Form} (d : Proof Γ p) : Proof (shifted Γ) p.shift :=
  d.shift.cast (by simp [negatives_shifted,Rewriting.shifts])

#print axioms up
#print axioms shiftProof
end PA215.PA.RelationalPredicateTemplate.ND
