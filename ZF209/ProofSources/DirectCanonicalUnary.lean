module
public import DirectCanonicalComposition
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

def ii_contract (Γ : Context) (a b : Formula) (p : Executable.Cert) :
 UnaryContract (.ii Γ a b p) p (.seq (a :: Γ) b) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 25
 emitted := rfl
 prefix_runs := context_two_formulas Γ a b
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_ii Γ a b actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem ii_evaluates (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.ii Γ a b p) :=
 unary_evaluates (ii_contract Γ a b p) ND.ii rfl (ii_runs Γ a b p) hp

def ce1_contract (Γ : Context) (a b : Formula) (p : Executable.Cert) :
 UnaryContract (.ce1 Γ a b p) p (.seq Γ (.and a b)) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 33
 emitted := rfl
 prefix_runs := context_two_formulas Γ a b
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_ce1 Γ a b actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem ce1_evaluates (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.ce1 Γ a b p) :=
 unary_evaluates (ce1_contract Γ a b p) ND.ce1 rfl (ce1_runs Γ a b p) hp

def ce2_contract (Γ : Context) (a b : Formula) (p : Executable.Cert) :
 UnaryContract (.ce2 Γ a b p) p (.seq Γ (.and a b)) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 35
 emitted := rfl
 prefix_runs := context_two_formulas Γ a b
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_ce2 Γ a b actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem ce2_evaluates (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.ce2 Γ a b p) :=
 unary_evaluates (ce2_contract Γ a b p) ND.ce2 rfl (ce2_runs Γ a b p) hp

def di1_contract (Γ : Context) (a b : Formula) (p : Executable.Cert) :
 UnaryContract (.di1 Γ a b p) p (.seq Γ a) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 37
 emitted := rfl
 prefix_runs := context_two_formulas Γ a b
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_di1 Γ a b actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem di1_evaluates (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.di1 Γ a b p) :=
 unary_evaluates (di1_contract Γ a b p) ND.di1 rfl (di1_runs Γ a b p) hp

def di2_contract (Γ : Context) (a b : Formula) (p : Executable.Cert) :
 UnaryContract (.di2 Γ a b p) p (.seq Γ b) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 39
 emitted := rfl
 prefix_runs := context_two_formulas Γ a b
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_di2 Γ a b actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem di2_evaluates (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.di2 Γ a b p) :=
 unary_evaluates (di2_contract Γ a b p) ND.di2 rfl (di2_runs Γ a b p) hp

def allI_contract (Γ : Context) (a : Formula) (p : Executable.Cert) :
 UnaryContract (.allI Γ a p) p (.seq (shiftContext Γ) a) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a
 operands := [.formula a,.context Γ]
 opcode := 47
 emitted := rfl
 prefix_runs := fun s => (SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_allI Γ a actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem allI_evaluates (Γ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.allI Γ a p) :=
 unary_evaluates (allI_contract Γ a p) ND.allI rfl (allI_runs Γ a p) hp

def allE_contract (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert) :
 UnaryContract (.allE Γ a t p) p (.seq Γ (.all a)) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitNat t
 operands := [.nat t,.formula a,.context Γ]
 opcode := 49
 emitted := rfl
 prefix_runs := fun s => ((SyntaxInterpreter.context_runs Γ s).append
   (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.nat_runs t _)
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_quantifier false Γ a t actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem allE_evaluates (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.allE Γ a t p) :=
 unary_evaluates (allE_contract Γ a t p) (ND.allE t) rfl (allE_runs Γ a t p) hp

def exI_contract (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert) :
 UnaryContract (.exI Γ a t p) p (.seq Γ (subst t a)) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitNat t
 operands := [.nat t,.formula a,.context Γ]
 opcode := 51
 emitted := rfl
 prefix_runs := fun s => ((SyntaxInterpreter.context_runs Γ s).append
   (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.nat_runs t _)
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_quantifier true Γ a t actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem exI_evaluates (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.exI Γ a t p) :=
 unary_evaluates (exI_contract Γ a t p) (ND.exI t) rfl (exI_runs Γ a t p) hp

end RosserDirect.ProofInterpreter
