module
public import FoundationTemplate
public import HeadSixTemplate
public import HeadFiveTemplate
public import HeadEqualityTemplates
public import NumericSemantics
@[expose] public section
namespace ZFR
open C207Soundness

/-- A literal finite subset of the ZFR fixed axiom list. -/
def coreContext : Context := [zfrRefl,zfrEqElem,zfrSym,zfrPair,zfrFoundation]

theorem coreContext_closed : ClosedContext coreContext := by
  intro p hp
  simp only [coreContext, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [zfrRefl,zfrEqElem,zfrSym,zfrPair,zfrFoundation,Bound]

theorem core_irreflexivity (i : Nat) : ND (.seq coreContext (.imp (.mem i i) .bot)) :=
  nd_irreflexivity (by simp [coreContext]) (by simp [coreContext])
    (by simp [coreContext]) (by simp [coreContext]) (by simp [coreContext]) i

theorem core_head1 (a d h : Nat) : ND (.seq coreContext (translateCode id (head1Code a d h))) :=
  nd_head1_code coreContext a d h

theorem core_head2 (a d h : Nat) : ND (.seq coreContext (translateCode id (head2Code a d h))) :=
  nd_head2_from_irreflexivity (by simp [coreContext]) core_irreflexivity d h

theorem core_head3 (a d h : Nat) : ND (.seq coreContext (translateCode id (head3Code a d h))) :=
  nd_head3_code (by simp [coreContext]) (by simp [coreContext]) a d h

theorem core_head4 (a d h : Nat) : ND (.seq coreContext (translateCode id (head4Code a d h))) :=
  nd_head4_code (by simp [coreContext]) (by simp [coreContext]) a d h

theorem core_head5 (a d h : Nat) : ND (.seq coreContext (translateCode id (head5Code a d h))) :=
  nd_head5_code coreContext a d h

theorem core_head6 (a d h : Nat) : ND (.seq coreContext (translateCode id (head6Code a d h))) :=
  nd_head6_from_irreflexivity core_irreflexivity d h

theorem core_rho8 (a d h v : Nat) : ND (.seq coreContext (translateCode id (rho8Code a d h v))) :=
  nd_rho8_code coreContext a d h v

end ZFR
