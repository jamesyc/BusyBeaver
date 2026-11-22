module
public import ZF192.Tape.History
public import ZF192Support.SetTheory.Omega.Translation

@[expose] public section
namespace ZF192
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory ZF192Support.OmegaInterpretation

/-- The literal halting predicate read in the natural numbers of ZF. -/
def literal192PhysicalSentence : SetTheorySentence :=
 arithmeticTranslation.translate BinaryTape.physicalHaltSentence
end ZF192
