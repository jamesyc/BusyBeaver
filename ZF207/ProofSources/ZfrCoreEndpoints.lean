module
public import NumericTheory
@[expose] public section
namespace ZFR
open C207Soundness

def ZfrProvable := sourceTheoryProvable sourceZfrAxiom

theorem zfr_head1 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head1Code a d h))) :=
 (core_head1 a d h).theoryProvable coreContext_in_zfr

theorem zfr_head2 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head2Code a d h))) :=
 (core_head2 a d h).theoryProvable coreContext_in_zfr

theorem zfr_head3 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head3Code a d h))) :=
 (core_head3 a d h).theoryProvable coreContext_in_zfr

theorem zfr_head4 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head4Code a d h))) :=
 (core_head4 a d h).theoryProvable coreContext_in_zfr

theorem zfr_head5 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head5Code a d h))) :=
 (core_head5 a d h).theoryProvable coreContext_in_zfr

theorem zfr_head6 (a d h : Nat) : ZfrProvable (encodeFormula (translateCode id (head6Code a d h))) :=
 (core_head6 a d h).theoryProvable coreContext_in_zfr

theorem zfr_rho8 (a d h v : Nat) : ZfrProvable (encodeFormula (translateCode id (rho8Code a d h v))) :=
 (core_rho8 a d h v).theoryProvable coreContext_in_zfr

end ZFR
