module
public import ZF192Support.Logic.Foundation.Axioms.Replacement.Functionality
public import ZF192Support.Logic.Foundation.Axioms.Replacement.Normalization
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- The actual Foundation schema follows from one concrete closed ZFR
Replacement instance and the fixed equality axioms. -/
theorem source_repOpen (p : SetTheorySemiproposition 2) :
 SourceTheorem (toSource (repOpen p)) := by
 let phi := toSource p
 let n := parameterBound phi
 have hb : Bound phi (n+2) := (parameterBound_valid phi).mono (by omega)
 let S := replacementSchema n phi
 let Γ := S :: equalitySourceContext
 have hs : SourceAxiom S := replacementSchema_in_zfr n phi hb
 refine ⟨Γ,?_,?_⟩
 · intro a ha
   rcases List.mem_cons.mp ha with h | h
   · subst a; exact hs
   · exact equalitySourceContext_in_zfr a h
 · apply ND.ie (repOpen_equiv p Γ).2
   apply ND.ii
   have hc : EqualityContext (totalUnique phi :: Γ) :=
     (equalitySourceContext_exact.cons S).cons (totalUnique phi)
   have hf := totalUnique_functional hc phi (ND.ctx List.mem_cons_self)
   exact ND.ie (nd_replacement_declose n phi hb (by simp [Γ,S])) hf

theorem source_replacement_axiom (p : SetTheorySemiproposition 2) :
 SourceTheorem (axiomSource (Axiom.replacementSchema p)) :=
 foundation_source_univCl (repOpen p) (source_repOpen p)

end ZFR.FoundationBridge
