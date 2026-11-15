module
public import ModelNativeAXSymbolicEval
@[expose] public section
set_option maxRecDepth 3000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXSymbolic
open ZFR.ArithmeticRepresentation ZF209.ModelCommands ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma t300_value (x y:M) : t300 x y=t299 x y+1 := by
 simp [t300,t299,t44,t30,t29,t28]
lemma t302_value (x y:M) : t302 x y=t299 x y+3 := by
 simp [t302,t299,t44,t32,t31,t30,t29,t28]
 norm_num
lemma t322_value (x y:M) : t322 x y=t299 y x+2 := by
 rw [modelAll_value,modelImp_value]
noncomputable def valuation (t a d h y x:M) : Fin 6→M := ![t,a,d,h,y,x]
lemma actual_spec (t a d h y x tail bottom:M) :
 materialize (valuation t a d h y x) tail bottom actualResult =
 ⟨t330 a (d+x) (h+y),a,d+x,h+y,tail,
 (heads a (d+x) (h+y) d h ++ [t]).foldr modelCantor bottom⟩ := by
 simp only [materialize,actualResult,listCode,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
 eval,valuation,Matrix.cons_val_zero,Matrix.cons_val_succ,heads,List.cons_append,List.nil_append,
 t323,t324,t325,t326,t327,t328,t329,t330,t300_value,t302_value,t322_value,t30,t29,t28]
 norm_num [Matrix.cons_val,add_assoc]
end ZF209.NativeAXSymbolic
