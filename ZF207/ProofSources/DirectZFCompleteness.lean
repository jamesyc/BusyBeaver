module
public import DirectZFDriver
public import DirectWitnessCoverage
@[expose] public section
namespace RosserDirect.ZFDriver
open Turing ZFR
/-- Same explicit finite-context content as ZFR.SourceTheorem, without loading
unrelated Foundation translation machinery into the finite checker closure. -/
abbrev SourceCertificate (f : Formula) :=
 ∃ Γ : Context, ExecutableZF.ValidContext Γ ∧ ND (.seq Γ f)

end RosserDirect.ZFDriver
