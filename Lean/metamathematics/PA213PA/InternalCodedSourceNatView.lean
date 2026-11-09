module

public import PA215PA.Theory
public import PA213PA.InternalCodedSourceExt
public import PA213PA.InternalFixedFile
public import PA215.Source.SeedPrefix

@[expose] public section
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open FixedTrace

noncomputable def encodeSource (c : Source.Configuration) : Nat :=
  stateCode (controlCode c.control) (fixedFile (List.ofFn c.registers))

def natView (c : Source.Configuration) : ModelSource.Configuration Nat := ⟨c.control,c.registers⟩

lemma encodeSource_store_valid (c : Source.Configuration) : ValidStore (store (encodeSource c)) := by
  simp [encodeSource,ValidStore,fixedFile_length]

lemma encodeSource_registers (c : Source.Configuration) :
    registers (store (encodeSource c))=c.registers := by
  funext r
  simp only [encodeSource,store_state,registers]
  rw [fixedFile_nth]
  simp only [natCast_nat,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos r.isLt,Option.getD_some]

private lemma sub_standard (a b : Nat) :
    @HSub.hSub Nat Nat Nat (@instHSub Nat instSub_foundation) a b =
      @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b := by
  symm
  apply Arithmetic.sub_eq_iff.mpr
  constructor
  · intro h
    simp only [Arithmetic.le_def] at h
    have hba : _root_.Nat.le b a := by
      rcases h with rfl | h
      · exact _root_.Nat.le_refl _
      · exact _root_.Nat.le_of_lt h
    exact (_root_.Nat.add_sub_of_le hba).symm
  · intro h
    exact _root_.Nat.sub_eq_zero_of_le (_root_.Nat.le_of_lt h)

lemma execute_natView (i : Source.Instruction) (rs : Source.Registers) :
    ModelSource.execute i rs=natView (Source.execute i rs) := by
  cases i with
  | inc r n => rfl
  | dec r z n =>
    by_cases h : rs r=0 <;> simp [ModelSource.execute,Source.execute,h,natView,
      PhysicalRegisters.write,Source.write]
    funext s
    simp only [PhysicalRegisters.write,Source.write,sub_standard]
  | jump n => rfl
  | halt => rfl

lemma restart_natView (c : Source.Configuration) :
    ModelSource.restart (natView c)=natView (Source.restart c) := by
  cases c with
  | mk q rs => cases q <;> rfl

lemma cycle_natView (c : Source.Configuration) :
    ModelSource.cycleStep (natView c)=natView (Source.cycleStep Source.exactSites c) := by
  unfold ModelSource.cycleStep Source.cycleStep
  have he : ModelSource.step (natView c)=natView (Source.step Source.exactSites c) := by
    cases c with
    | mk q rs =>
      cases q with
      | «at» i =>
        cases hr : Source.resolveAt Source.exactSites i with
        | none => simp [ModelSource.step,Source.step,natView,hr]
        | some inst => simpa [ModelSource.step,Source.step,natView,hr] using execute_natView inst rs
      | halted => rfl
      | exited => rfl
      | malformed => rfl
  rw [he,restart_natView]

#print axioms encodeSource_registers
#print axioms cycle_natView
end PA213.PA.InternalTrace.CodedSource

