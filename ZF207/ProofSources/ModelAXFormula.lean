module
public import ModelPushFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZF207.MM0ModelReplay ZF207.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Actual first-order AX formula. Constructor certificates are explicit;
no Sigma1 classification of the assembled formula is asserted here. -/
noncomputable def axFormula (ρ:Nat → M) : ArithmeticSemiformula Nat 11 :=
 let c322:=literalC207Constructor322_certificate ρ
 let c323:=literalC207Constructor323_certificate ρ
 let c324:=literalC207Constructor324_certificate ρ
 let c325:=literalC207Constructor325_certificate ρ
 let c326:=literalC207Constructor326_certificate ρ
 let c327:=literalC207Constructor327_certificate ρ
 let c328:=literalC207Constructor328_certificate ρ
 let c329:=literalC207Constructor329_certificate ρ
 let c330:=literalC207Constructor330_certificate ρ
“a x y t w d h u v dd hh. ∃d1, ∃h1, d1=d+x ∧ h1=h+y ∧ dd=0 ∧ hh=0 ∧
 ((a≠d1 ∧ a≠h1 ∧ !c330.formula u a d1 h1) ∨ ((a=d1 ∨ a=h1) ∧ u=0)) ∧
 ∃q1, ∃q2, ∃q3, ∃q4, ∃q5, ∃q6, ∃q7, ∃q8,
 !c323.formula q1 a d1 h1 ∧ !c324.formula q2 a d1 h1 ∧ !c325.formula q3 a d1 h1 ∧ !c326.formula q4 a d1 h1 ∧ !c327.formula q5 a d1 h1 ∧ !c328.formula q6 a d1 h1 ∧ !c329.formula q7 a d1 h1 d ∧ !c322.formula q8 d h ∧
 ∃s0, ∃s1, ∃s2, ∃s3, ∃s4, ∃s5, ∃s6, ∃s7,
 !literalPairGraph s0 t w ∧ !literalPairGraph s1 q8 s0 ∧ !literalPairGraph s2 q7 s1 ∧ !literalPairGraph s3 q6 s2 ∧ !literalPairGraph s4 q5 s3 ∧ !literalPairGraph s5 q4 s4 ∧ !literalPairGraph s6 q3 s5 ∧ !literalPairGraph s7 q2 s6 ∧ !literalPairGraph v q1 s7”
lemma axFormula_eval (ρ:Nat → M) (a x y t w d h u v dd hh:M) :
 (axFormula ρ).Eval ![a,x,y,t,w,d,h,u,v,dd,hh] ρ ↔
 modelCommandEval (.ax a x y) ⟨t,w,d,h⟩ = some ⟨u,v,dd,hh⟩ := by
 have h322 (z a b:M) : (literalC207Constructor322_certificate ρ).formula.Eval ![z,a,b] ρ ↔ z=t322 a b := (literalC207Constructor322_certificate ρ).correct ![a,b] z
 have h323 (z a b c:M) : (literalC207Constructor323_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t323 a b c := (literalC207Constructor323_certificate ρ).correct ![a,b,c] z
 have h324 (z a b c:M) : (literalC207Constructor324_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t324 a b c := (literalC207Constructor324_certificate ρ).correct ![a,b,c] z
 have h325 (z a b c:M) : (literalC207Constructor325_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t325 a b c := (literalC207Constructor325_certificate ρ).correct ![a,b,c] z
 have h326 (z a b c:M) : (literalC207Constructor326_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t326 a b c := (literalC207Constructor326_certificate ρ).correct ![a,b,c] z
 have h327 (z a b c:M) : (literalC207Constructor327_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t327 a b c := (literalC207Constructor327_certificate ρ).correct ![a,b,c] z
 have h328 (z a b c:M) : (literalC207Constructor328_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t328 a b c := (literalC207Constructor328_certificate ρ).correct ![a,b,c] z
 have h329 (z a b c d:M) : (literalC207Constructor329_certificate ρ).formula.Eval ![z,a,b,c,d] ρ ↔ z=t329 a b c d := (literalC207Constructor329_certificate ρ).correct ![a,b,c,d] z
 have h330 (z a b c:M) : (literalC207Constructor330_certificate ρ).formula.Eval ![z,a,b,c] ρ ↔ z=t330 a b c := (literalC207Constructor330_certificate ρ).correct ![a,b,c] z
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [axFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,
h322,h323,h324,h325,h326,h327,h328,h329,h330,literalPairGraph_eval,literalPair_modelCantor,exists_eq_left]
 by_cases hg:a≠d+x ∧ a≠h+y
 · simp [modelCommandEval,gate,heads,hg,eq_comm,and_assoc,and_comm,and_left_comm]
 · have hn : a=d+x ∨ a=h+y := by tauto
   rcases hn with hn|hn <;> simp [modelCommandEval,gate,heads,hg,hn,eq_comm,and_assoc,and_comm,and_left_comm]
/-- Freeze the constructor expression once; its syntax is independent of the model. -/
noncomputable def fixedAXFormula : ArithmeticSemiformula Nat 11 := axFormula (M:=Nat) (fun _=>0)
lemma axFormula_fixed (ρ:Nat → M) : axFormula ρ=fixedAXFormula := by rfl
lemma fixedAXFormula_eval (ρ:Nat → M) (a x y t w d h u v dd hh:M) :
 fixedAXFormula.Eval ![a,x,y,t,w,d,h,u,v,dd,hh] ρ ↔
 modelCommandEval (.ax a x y) ⟨t,w,d,h⟩ = some ⟨u,v,dd,hh⟩ := by
 rw [←axFormula_fixed ρ]
 exact axFormula_eval ρ a x y t w d h u v dd hh
end ZF207.ModelCommands
