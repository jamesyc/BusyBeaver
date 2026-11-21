module
public import I3_380.Search.Compiler.Program
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Typed
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The twelve arithmetic-model registers use Foundation's vector coding.
The declarative program and its model trace share the same store API. -/
noncomputable def Store.code (s : Store M) : M := matrixToVec s

noncomputable def Store.ofCode (code : M) : Store M :=
  fun r => code.[(r.val : M)]

@[simp] theorem Store.len_code (s : Store M) : len s.code = (12 : M) := by
  unfold Store.code
  exact (matrixToVec_len s).trans (Nat.cast_ofNat)

@[simp] theorem Store.ofCode_code (s : Store M) : Store.ofCode s.code = s := by
  funext r
  exact matrixToVec_nth s r

theorem Store.code_ofCode {code : M} (wellFormed : len code = (12 : M)) :
    (Store.ofCode code).code = code := by
  apply nth_ext' (len code) (by rw [Store.len_code,wellFormed]) rfl
  intro i hi
  have standard : i < ((12 : Nat) : M) := by exact_mod_cast (wellFormed ▸ hi)
  have numeralBound : i < ORingStructure.numeral 12 := by rwa [numeral_eq_natCast]
  obtain ⟨r,same⟩ := (lt_numeral_iff (n := 12)).mp numeralBound
  rw [numeral_eq_natCast] at same
  subst i
  exact matrixToVec_nth (Store.ofCode code) r

/-- Code construction for a fixed number of definable fields. Model-finite
sequences of such stores use the separate trace lemmas. -/
theorem matrixToVec_definable₁ {n : Nat} (fields : Fin n → M → M)
    (defined : ∀ i, 𝚺ᴬ₁-Function₁ (fields i)) :
    𝚺ᴬ₁-Function₁ (fun x => matrixToVec (fun i => fields i x)) := by
  induction n with
  | zero => simp only [matrixToVec_nil]; definability
  | succ n ih =>
    have head := defined 0
    have tail := ih (fun i => fields i.succ) (fun i => defined i.succ)
    simp only [matrixToVec_succ,Matrix.vecHead,Matrix.vecTail]
    definability

theorem Store.read_definable (r : Register) :
    𝚺ᴬ₁-Function₁ (fun code : M => Store.ofCode code r) := by
  unfold Store.ofCode
  definability

noncomputable def Store.writeCode (r : Register) (code value : M) : M :=
  ((Store.ofCode code).set r value).code

theorem Store.writeCode_definable (r : Register) :
    𝚺ᴬ₁-Function₂ (Store.writeCode (M := M) r) := by
  let fields := fun (i : Register) (pair : M) => if i = r then π₂ pair else (π₁ pair).[(i.val : M)]
  have individual (i : Register) : 𝚺ᴬ₁-Function₁ (fields i) := by
    by_cases hi : i = r
    · simp only [fields,hi,↓reduceIte]
      definability
    · simp only [fields,hi,↓reduceIte]
      definability
  let build := fun pair : M => matrixToVec (fun i => fields i pair)
  have function : 𝚺ᴬ₁-Function₁ build := matrixToVec_definable₁ fields individual
  have reduce : Store.writeCode (M := M) r = fun code value => build ⟪code,value⟫ := by
    funext code value
    unfold Store.writeCode Store.code build
    congr 1
    funext i
    simp only [Store.set,Store.ofCode,fields,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
  have pairDefinable : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 2 → M => ⟪v 0,v 1⟫) := by definability
  letI : 𝚺ᴬ₁-Function₁ build := function
  exact reduce.symm ▸
    Bounding.HierarchySymbol.DefinableFunction₁.comp (F := build) pairDefinable

end PalomarI3380.Compiler
