module
public import ModelReplay1143
public import ExactRadix8Graphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalLe_order (a b : M) : t47 a b ↔ a≤b := by
 classical
 simp [t47,t9,t1,t8,t10,t44,le_iff_exists_add,eq_comm]
lemma literalLt_order (a b : M) : t48 a b ↔ a<b := by
 change t47 (a+1) b ↔ a<b
 rw [literalLe_order,succ_le_iff_lt]
lemma literalDivMod_equation (n d : M) : d*t56 n d+t57 n d=n := p1077 n d
lemma literalMod_lt (n d : M) (hd : d≠0) : t57 n d<d := by
 apply (literalLt_order _ _).mp
 apply p1078 n d
 exact hd
lemma literalDiv8_value (n : M) : t56 n 8=graphValue radix8QuotientGraph radix8QuotientGraph_total ![n] := by
 apply (graphValue_spec radix8QuotientGraph radix8QuotientGraph_total _ _).mp
 apply (radix8QuotientGraph_eval _ _).mpr
 exact ⟨t57 n 8,literalMod_lt n 8 (by simp),(literalDivMod_equation n 8).symm⟩
lemma literalMod8_value (n : M) : t57 n 8=graphValue radix8ResidueGraph radix8ResidueGraph_total ![n] := by
 apply (graphValue_spec radix8ResidueGraph radix8ResidueGraph_total _ _).mp
 apply (radix8ResidueGraph_eval _ _).mpr
 exact ⟨literalMod_lt n 8 (by simp),t56 n 8,(literalDivMod_equation n 8).symm⟩
end ZF207.MM0ModelReplay
