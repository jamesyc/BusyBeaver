module
public import I3_334.Calibration.ModelRegisters
public import I3_334Support.Search.Arithmetic.CodedLines
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines inc move clear coded_increment coded_move coded_clear
  coded_unpair)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Pack the four model-valued dictionary entries in the literal order. -/
noncomputable def modelDictionary (entry : Fin 4 → M) : M :=
  pairValue (pairValue (pairValue (entry 3) (entry 2)) (entry 1)) (entry 0)

noncomputable def dictionaryLeft : Nat → M → M
  | 0, word => word
  | n+1, word => decodeLeft (dictionaryLeft n word)

noncomputable def modelSlot (word : M) (slot : Fin 4) : M :=
  let rest := dictionaryLeft slot.val word
  if slot.val < 3 then decodeRight rest else rest

theorem modelSlot_dictionary (entry : Fin 4 → M) (slot : Fin 4) :
    modelSlot (modelDictionary entry) slot = entry slot := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [modelSlot,dictionaryLeft,modelDictionary,decode_pairValue]

theorem coded_increments (r : Register) (count : Nat) (s : Store M) :
    CodedLines (List.replicate count (inc r)) s.code (s.set r (s r+(count : M))).code := by
  induction count generalizing s with
  | zero =>
    simp only [List.replicate_zero,Nat.cast_zero,add_zero,Store.set_same]
    exact .nil _
  | succ n ih =>
    have rest := ih (s.set r (s r+1))
    rw [Store.get_set,Store.set_set,add_right_comm] at rest
    simpa only [List.replicate_succ,Nat.cast_succ,add_assoc] using
      CodedLines.cons (coded_increment r s) rest

theorem coded_dictionaryPart (takeLeft : Bool) (s : Store M)
    (freeExpected : s expected = 0) (freeAux : s u = 0) :
    (dictionaryPart takeLeft).Runs .normal s.code
      (s.set tmp (if takeLeft then decodeLeft (s tmp) else decodeRight (s tmp))).code := by
  let a := decodeLeft (s tmp)
  let b := decodeRight (s tmp)
  let split := ((s.set tmp 0).set expected a).set u b
  have first : (Source.unpair expected u tmp).Runs .normal s.code split.code :=
    coded_unpair (by decide) (by decide) (by decide) s freeExpected freeAux
  cases takeLeft
  · let moved := (split.set u 0).set tmp (split tmp + split u)
    have second : (move u tmp).Runs .normal split.code moved.code := coded_move (by decide) split
    have cleanup := coded_clear expected moved
    have final : moved.set expected 0 = s.set tmp b := by
      funext i
      by_cases x : i = tmp <;> by_cases y : i = expected <;> by_cases z : i = u <;>
        simp [moved,split,Store.set,x,y,z,tmp,expected,u,freeExpected,freeAux]
    rw [final] at cleanup
    exact Program.Runs.rightExit first (Program.Runs.rightExit second cleanup rfl) rfl
  · let moved := (split.set expected 0).set tmp (split tmp + split expected)
    have second : (move expected tmp).Runs .normal split.code moved.code := coded_move (by decide) split
    have cleanup := coded_clear u moved
    have final : moved.set u 0 = s.set tmp a := by
      funext i
      by_cases x : i = tmp <;> by_cases y : i = expected <;> by_cases z : i = u <;>
        simp [moved,split,Store.set,x,y,z,tmp,expected,u,freeExpected,freeAux]
    rw [final] at cleanup
    exact Program.Runs.rightExit first (Program.Runs.rightExit second cleanup rfl) rfl

theorem coded_dictionarySlot (slot : Fin 4) (s : Store M) (clean : Scratch s) :
    CodedLines (dictionarySlot slot) s.code (s.set tmp (modelSlot (s tmp) slot)).code := by
  let select := fun (left : Bool) (n : M) => if left then decodeLeft n else decodeRight n
  have step (left : Bool) (word : M) :
      (dictionaryPart left).Runs .normal (s.set tmp word).code (s.set tmp (select left word)).code := by
    have run := coded_dictionaryPart left (s.set tmp word)
      (by simpa [Store.set,tmp,expected] using clean.expectedEmpty)
      (by simpa [Store.set,tmp,u] using clean.auxiliaryEmpty)
    simpa only [Store.get_set,Store.set_set,select] using run
  have start (left : Bool) :
      (dictionaryPart left).Runs .normal s.code (s.set tmp (select left (s tmp))).code := by
    simpa only [Store.set_same] using step left (s tmp)
  have slots : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases slots with rfl | rfl | rfl | rfl
  · exact .cons (start false) (.nil _)
  · exact .cons (start true) (.cons (step false (decodeLeft (s tmp))) (.nil _))
  · exact .cons (start true) (.cons (step true (decodeLeft (s tmp)))
      (.cons (step false (decodeLeft (decodeLeft (s tmp)))) (.nil _)))
  · exact .cons (start true) (.cons (step true (decodeLeft (s tmp)))
      (.cons (step true (decodeLeft (decodeLeft (s tmp)))) (.nil _)))

end PalomarI3334.SearchProgram
