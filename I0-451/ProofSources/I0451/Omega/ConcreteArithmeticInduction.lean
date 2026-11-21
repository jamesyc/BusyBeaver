module
public import I0451.Omega.ConcreteArithmeticModelStructure
public import I0451.Omega.ConcreteArithmeticTranslation
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
def ofOmega (x : V) (hx : x ∈ (ω : V)) : A :=
 ⟨x, by simpa [DirectTranslation.Dom,arithmeticTranslation,Semiformula.Operator.val] using hx⟩
@[simp] theorem val_add_one (x : A) : (x+1).val = succ x.val := by
 rw [val_add,val_one]
 have h1 : (1 : V) = succ 0 := by simp [one_def,zero_def,succ]
 rw [h1,add_succ _ _ zero_mem_ω,add_zero]
theorem translated_eval (p : Semiformula ℒₒᵣ Nat 1) (s : Nat → A) (x : A) :
 (arithmeticTranslation.translate p).Eval ![x.val] (fun i => (s i).val) ↔ p.Eval ![x] s := by
 have he : (fun i : Fin 1 => (![x] i).val) = ![x.val] := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl
 have h := (DirectTranslation.Model.eval_translate_iff (π := arithmeticTranslation) (M := V) (φ := p) (e := ![x]) (ε := s))
 rw [interpreted_structure_eq_standard (V := V)] at h
 simpa only [he] using h

theorem arithmetic_formula_induction (p : Semiformula ℒₒᵣ Nat 1) (s : Nat → A)
 (hz : p.Eval ![0] s) (hs : ∀ x : A, p.Eval ![x] s → p.Eval ![x+1] s) :
 ∀ x : A, p.Eval ![x] s := by
 let P : V → Prop := fun x => (arithmeticTranslation.translate p).Eval ![x] (fun i => (s i).val)
 have hp : ℒₛₑₜ-predicate P := by
  refine ⟨(Rew.rewriteMap (fun i => (s i).val)) ▹ (arithmeticTranslation.translate p),?_⟩
  intro v
  simp only [Semiformula.eval_rewriteMap,Function.comp_def,id_eq]
  rw [Matrix.fun_eq_vec_one v]
  rfl
 have hzero : P 0 := by
  have h := (translated_eval p s (0 : A)).mpr hz
  simpa only [val_zero] using h
 have hsucc : ∀ x : V, x ∈ (ω : V) → P x → P (succ x) := by
  intro x hx ih
  let a : A := ofOmega x hx
  have hpa : p.Eval ![a] s := (translated_eval p s a).mp ih
  have h := (translated_eval p s (a+1)).mpr (hs a hpa)
  simpa only [val_add_one, a, ofOmega] using h
 intro x
 exact (translated_eval p s x).mp (naturalNumber_induction P hp hzero hsucc x.val (model_mem_omega x))
instance models_arithmetic_induction : A↓[ℒₒᵣ] ⊧* Arithmetic.InductionScheme ℒₒᵣ Set.univ := by
 apply models_theory_iff.mpr
 intro σ hσ
 obtain ⟨p,_,rfl⟩ := hσ
 rw [models_iff_proposition]
 intro s
 simpa [Arithmetic.succInd] using arithmetic_formula_induction p s
end ZF207.OmegaInterpretation
