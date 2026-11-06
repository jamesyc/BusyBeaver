import PA215PA.FoundationNativeRefutationInternal
import PA215PA.InternalActualRefutationSentences
import PA215PA.Foundation

/-! The actual checker consistency statement implies Foundation's exact PA
consistency sentence internally. The logical proof-code adapter is now paid. -/
namespace PA215.PA.InternalActualRefutation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

theorem pa_proves_no_actual_refutation_consistency :
    theory ⊢ noActualRefutationSentence 🡒 consistencySentence :=by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply]
  intro hn
  have hno:=noActualRefutation_correct (V:=V) |>.mp hn
  have hc:theory.Consistent V:=by
    intro hp
    have hp':Provable theory (qqFalsum:V):=by simpa only [Sentence.quote_falsum] using hp
    obtain ⟨code,hcode⟩:=FoundationNativeRefutationTransport.original_provable_refutation_transport hp'
    exact hno code hcode
  simpa [consistencySentence] using hc
#print axioms pa_proves_no_actual_refutation_consistency
end PA215.PA.InternalActualRefutation
