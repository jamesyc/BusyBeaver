module
public import ConcreteArithmeticModelOperations
public import Foundation.FirstOrder.Arithmetic.Basic
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
noncomputable instance omegaORingStructure : ORingStructure (arithmeticTranslation.Model V) where
 zero := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.zero ![]
 one := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.one ![]
 add x y := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.add ![x,y]
 mul x y := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul ![x,y]
 lt x y := Tarski.Structure.rel (L := ℒₒᵣ) Language.ORing.Rel.lt ![x,y]
local notation "A" => arithmeticTranslation.Model V
@[simp] theorem val_zero : (0 : A).val = (0 : V) := by
 change (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.zero (![] : Fin 0 → A)).val = (0 : V)
 exact (model_zero_value (V := V)).trans zero_def.symm
@[simp] theorem val_one : (1 : A).val = (1 : V) := by
 change (Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.one (![] : Fin 0 → A)).val = (1 : V)
 exact (model_one_value (V := V)).trans (by simp [one_def,zero_def,succ])
@[simp] theorem val_add (x y : A) : (x+y).val = add x.val y.val := model_add_value x y
@[simp] theorem val_mul (x y : A) : (x*y).val = mul x.val y.val := model_mul_value x y
@[simp] theorem lt_iff_mem (x y : A) : x<y ↔ x.val ∈ y.val := model_lt_iff x y
/-- Arithmetic's standard structure and the relational interpretation structure
are extensionally equal. Downstream PA theorems therefore concern the exact
same induced operations, not an independently supplied arithmetic model. -/
theorem interpreted_structure_eq_standard :
 DirectTranslation.Model.struc arithmeticTranslation V = Arithmetic.standardModel A := by
 apply Tarski.Structure.ext
 · funext k f v
   cases f
   all_goals try simp only [Arithmetic.standardModel,omegaORingStructure]
   all_goals congr 1 <;> funext i
   all_goals first | exact Fin.elim0 i | exact congrFun (Matrix.fun_eq_vec_two v) i
 · funext k r v
   cases r
   · apply propext
     exact DirectTranslation.Model.eq_iff v
   · change @Tarski.Structure.rel _ _ (DirectTranslation.Model.struc arithmeticTranslation V) _ Language.ORing.Rel.lt v =
       @Tarski.Structure.rel _ _ (DirectTranslation.Model.struc arithmeticTranslation V) _ Language.ORing.Rel.lt ![v 0,v 1]
     rw [← Matrix.fun_eq_vec_two v]
end ZF207.OmegaInterpretation
