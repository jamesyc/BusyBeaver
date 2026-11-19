module
public import ModelCommandSemantics
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZF207.MM0ModelReplay ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma modelCommandsEval_append (xs ys:List (Command M)) (s:Store M) :
 modelCommandsEval (xs++ys) s=(modelCommandsEval xs s).bind (modelCommandsEval ys) := by
 induction xs generalizing s with
 | nil => rfl
 | cons c cs ih => simp only [List.cons_append,modelCommandsEval,Option.bind_assoc,ih]
lemma scaffold8 (g x1 x2 x3 x4 x5 x6 r q t w:M) :
 modelCommandsEval (List.replicate 8 (.shift : Command M))
 ⟨4*g,[4*x1,4*x2,4*x3,4*x4,4*x5,4*x6,4*r,4*q+2,t].foldr modelCantor w,0,0⟩ =
 some ⟨4*r,modelCantor t w,0,4*q+2⟩ := by
 have ez:4*g+0≠(1:M) := by simpa using four_mul_ne_one g
 have e1:(0:M)+4*x1≠1 := by simpa using four_mul_ne_one x1
 have ee (a b:M) : 4*a+4*b≠1 := by rw [←mul_add]; exact four_mul_ne_one _
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 modelCommandsEval,modelCommandEval,modelUnpairLeft_pair,modelUnpairRight_pair,
 ez,e1,ee,ite_false,Option.bind_some]
lemma gate_multiple (a d h:M) : ∃q,gate a d h=4*q := by
 unfold gate
 split
 · unfold t330; rw [modelImp_value]; exact ⟨_,rfl⟩
 · exact ⟨0,by simp⟩
lemma h323_multiple (a d h:M) : ∃q,t323 a d h=4*q := by
 unfold t323; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h324_multiple (a d h:M) : ∃q,t324 a d h=4*q := by
 unfold t324; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h325_multiple (a d h:M) : ∃q,t325 a d h=4*q := by
 unfold t325; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h326_multiple (a d h:M) : ∃q,t326 a d h=4*q := by
 unfold t326; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h327_multiple (a d h:M) : ∃q,t327 a d h=4*q := by
 unfold t327; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h328_multiple (a d h:M) : ∃q,t328 a d h=4*q := by
 unfold t328; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma h329_multiple (a d h u:M) : ∃q,t329 a d h u=4*q := by
 unfold t329; rw [modelImp_value]; exact ⟨_,rfl⟩
lemma modelAX_shift8 (a x y t w d h:M) :
 modelCommandsEval ([.ax a x y]++List.replicate 8 .shift) ⟨t,w,d,h⟩ =
 some ⟨t329 a (d+x) (h+y) d,modelCantor t w,0,t322 d h⟩ := by
 rw [modelCommandsEval_append]
 change modelCommandsEval (List.replicate 8 .shift) ⟨gate a (d+x) (h+y),
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
  scaffold8 g q1 q2 q3 q4 q5 q6 qr (modelCantor h d) t w
/-- Fixed ten-command macro, symbolic arbitrary PA-model stores. Not yet coded arbitrary-length traces. -/
lemma modelPUSH_total (t w d h:M) :
 modelCommandsEval (([.ax 0 0 0]++List.replicate 8 .shift)++[.mp 0]) ⟨t,w,d,h⟩ =
 some ⟨0,modelCantor t w,0,0⟩ := by
 rw [modelCommandsEval_append,modelAX_shift8]
 have he:t299 (t329 0 (d+0) (h+0) d) (0+0) ≠ t322 d h := by
  rw [modelImp_value,modelAll_value]
  exact four_mul_ne_four_add_two _ _
 simp only [add_zero] at he
 simp only [Option.bind_some,modelCommandsEval,modelCommandEval,he,ite_false,add_zero]
end ZF207.ModelCommands
