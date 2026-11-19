module
public import ModelSupplyHelpers
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZF207.MM0ModelReplay ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma scaffold2 (g x1 x2 x3 x4 x5 x6 r q t w:M) :
 modelCommandsEval (List.replicate 2 (.shift:Command M))
 ⟨4*g,[4*x1,4*x2,4*x3,4*x4,4*x5,4*x6,4*r,4*q+2,t].foldr modelCantor w,0,0⟩ =
 some ⟨4*x1,[4*x3,4*x4,4*x5,4*x6,4*r,4*q+2,t].foldr modelCantor w,0,4*x2⟩ := by
 have ez:4*g+0≠(1:M) := by simpa using four_mul_ne_one g
 have e1:(0:M)+4*x1≠1 := by simpa using four_mul_ne_one x1
 have ee (a b:M) : 4*a+4*b≠1 := by rw [←mul_add]; exact four_mul_ne_one _
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 modelCommandsEval,modelCommandEval,modelUnpairLeft_pair,modelUnpairRight_pair,ez,e1,ee,ite_false,Option.bind_some]
lemma modelAX_shift2 (a x y t w d h:M) :
 modelCommandsEval ([.ax a x y]++List.replicate 2 .shift) ⟨t,w,d,h⟩ =
 some ⟨t323 a (d+x) (h+y),[t325 a (d+x) (h+y),t326 a (d+x) (h+y),t327 a (d+x) (h+y),t328 a (d+x) (h+y),t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t324 a (d+x) (h+y)⟩ := by
 rw [modelCommandsEval_append]
 change modelCommandsEval (List.replicate 2 .shift) ⟨gate a (d+x) (h+y),
  (heads a (d+x) (h+y) d h++[t]).foldr modelCantor w,0,0⟩=_
 obtain ⟨g,hg⟩:=gate_multiple a (d+x) (h+y)
 obtain ⟨q1,h1⟩:=h323_multiple a (d+x) (h+y)
 obtain ⟨q2,h2⟩:=h324_multiple a (d+x) (h+y)
 obtain ⟨q3,h3⟩:=h325_multiple a (d+x) (h+y)
 obtain ⟨q4,h4⟩:=h326_multiple a (d+x) (h+y)
 obtain ⟨q5,h5⟩:=h327_multiple a (d+x) (h+y)
 obtain ⟨q6,h6⟩:=h328_multiple a (d+x) (h+y)
 obtain ⟨qr,hr⟩:=h329_multiple a (d+x) (h+y) d
 simpa only [heads,hg,h1,h2,h3,h4,h5,h6,hr,modelAll_value,List.cons_append,List.nil_append] using
  scaffold2 g q1 q2 q3 q4 q5 q6 qr (modelCantor h d) t w
end ZF207.ModelCommands
