module
public import ModelReplay1270
public import ExactCantorGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The ORIGINAL MM0 pairing value equals the independently represented exact Cantor function in every PA model. -/
lemma literalPair_modelCantor (a b : M) : t63 a b=modelCantor a b := by
 have hd := p1126 (t45 (t44 a b) (t29 (t44 a b))) t31 (p1251 (t44 a b))
 change t56 ((a+b)*((a+b)+1)) 2 * 2=(a+b)*((a+b)+1) at hd
 apply modelCantor_unique
 change 2*(t56 ((a+b)*((a+b)+1)) 2+b)=(a+b)*((a+b)+1)+2*b
 rw [mul_add,mul_comm 2,hd]
end ZF207.MM0ModelReplay
