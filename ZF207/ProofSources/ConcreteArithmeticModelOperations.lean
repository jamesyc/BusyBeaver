module
public import ConcreteArithmeticTranslation
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
attribute [local irreducible] add mul
@[simp] theorem model_mem_omega (x : A) : x.val ∈ (ω : V) := by
 simpa [DirectTranslation.Dom,arithmeticTranslation,Semiformula.Operator.val] using x.dom
@[simp] theorem model_zero_value : (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.zero (![] : Fin 0 → A)).val = (∅ : V) := by
 simpa [arithmeticTranslation,arithmeticFuncGraph,Semiformula.Operator.val] using
  (DirectTranslation.Model.eval_func (π := arithmeticTranslation) (M := V) Language.ORing.Func.zero (![] : Fin 0 → A))
@[simp] theorem model_one_value : (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.one (![] : Fin 0 → A)).val = succ (∅ : V) := by
 simpa [arithmeticTranslation,arithmeticFuncGraph,Semiformula.Operator.val] using
  (DirectTranslation.Model.eval_func (π := arithmeticTranslation) (M := V) Language.ORing.Func.one (![] : Fin 0 → A))
@[simp] theorem model_add_value (x y : A) : (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.add ![x,y]).val = add x.val y.val := by
 simpa [arithmeticTranslation,arithmeticFuncGraph,Semiformula.Operator.val,add_graph_defined.iff] using
  (DirectTranslation.Model.eval_func (π := arithmeticTranslation) (M := V) Language.ORing.Func.add ![x,y])
@[simp] theorem model_mul_value (x y : A) : (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul ![x,y]).val = mul x.val y.val := by
 simpa [arithmeticTranslation,arithmeticFuncGraph,Semiformula.Operator.val,mul_graph_defined.iff] using
  (DirectTranslation.Model.eval_func (π := arithmeticTranslation) (M := V) Language.ORing.Func.mul ![x,y])
@[simp] theorem model_lt_iff (x y : A) : Tarski.Structure.rel (L := ℒₒᵣ) Language.ORing.Rel.lt ![x,y] ↔ x.val ∈ y.val := by
 simpa [arithmeticTranslation,arithmeticRelGraph,Semiformula.Operator.val,Semiformula.Operator.Mem.sentence_eq] using
  (DirectTranslation.Model.rel_iff (π := arithmeticTranslation) (M := V) Language.ORing.Rel.lt ![x,y])
end ZF207.OmegaInterpretation
