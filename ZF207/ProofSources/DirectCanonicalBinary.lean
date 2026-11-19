module
public import DirectCanonicalBinaryComposition
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

def ie_contract (Γ : Context) (a b : Formula) (p q : Executable.Cert) :
 BinaryContract (.ie Γ a b p q) p q (.seq Γ (.imp a b)) (.seq Γ a) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 27
 emitted := rfl
 prefix_runs := fun s => (((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.formula_runs b _))
 mismatch := by
   intro r₁ r₂ hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_ie Γ a b r₂ r₁ hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem ie_evaluates (Γ : Context) (a b : Formula) (p q : Executable.Cert)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates (.ie Γ a b p q) :=
 binary_evaluates (ie_contract Γ a b p q) ND.ie rfl (ie_runs Γ a b p q) hp hq

def ci_contract (Γ : Context) (a b : Formula) (p q : Executable.Cert) :
 BinaryContract (.ci Γ a b p q) p q (.seq Γ a) (.seq Γ b) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b
 operands := [.formula b,.formula a,.context Γ]
 opcode := 31
 emitted := rfl
 prefix_runs := fun s => (((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.formula_runs b _))
 mismatch := by
   intro r₁ r₂ hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_ci Γ a b r₂ r₁ hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem ci_evaluates (Γ : Context) (a b : Formula) (p q : Executable.Cert)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates (.ci Γ a b p q) :=
 binary_evaluates (ci_contract Γ a b p q) ND.ci rfl (ci_runs Γ a b p q) hp hq

def branchPair_contract (Γ : Context) (a b c : Formula) (p q : Executable.Cert) :
 BinaryContract (.branchPair Γ a b c p q) p q (.seq (a :: Γ) c) (.seq (b :: Γ) c) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b ++ TokenVM.emitFormula c
 operands := [.formula c,.formula b,.formula a,.context Γ]
 opcode := 41
 emitted := rfl
 prefix_runs := fun s => ((((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.formula_runs b _)).append (SyntaxInterpreter.formula_runs c _))
 mismatch := by
   intro r₁ r₂ hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_branchPair Γ a b c r₂ r₁ hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem branchPair_evaluates (Γ : Context) (a b c : Formula) (p q : Executable.Cert)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates (.branchPair Γ a b c p q) :=
 binary_evaluates (branchPair_contract Γ a b c p q) ND.branchPair rfl (branchPair_runs Γ a b c p q) hp hq

def de_contract (Γ : Context) (a b c : Formula) (p q : Executable.Cert) :
 BinaryContract (.de Γ a b c p q) p q (.seq Γ (.or a b)) (.branches Γ a b c) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b ++ TokenVM.emitFormula c
 operands := [.formula c,.formula b,.formula a,.context Γ]
 opcode := 43
 emitted := rfl
 prefix_runs := fun s => ((((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.formula_runs b _)).append (SyntaxInterpreter.formula_runs c _))
 mismatch := by
   intro r₁ r₂ hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_de Γ a b c r₂ r₁ hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem de_evaluates (Γ : Context) (a b c : Formula) (p q : Executable.Cert)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates (.de Γ a b c p q) :=
 binary_evaluates (de_contract Γ a b c p q) ND.de rfl (de_runs Γ a b c p q) hp hq

def exE_contract (Γ : Context) (a c : Formula) (p q : Executable.Cert) :
 BinaryContract (.exE Γ a c p q) p q (.seq Γ (.ex a)) (.seq (a :: shiftContext Γ) (shift c)) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula c
 operands := [.formula c,.formula a,.context Γ]
 opcode := 53
 emitted := rfl
 prefix_runs := fun s => (((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append (SyntaxInterpreter.formula_runs c _))
 mismatch := by
   intro r₁ r₂ hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_exE Γ a c r₂ r₁ hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩
theorem exE_evaluates (Γ : Context) (a c : Formula) (p q : Executable.Cert)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates (.exE Γ a c p q) :=
 binary_evaluates (exE_contract Γ a c p q) ND.exE rfl (exE_runs Γ a c p q) hp hq

end RosserDirect.ProofInterpreter
