module
public import I3_334Support.Machine
public import I3_334Support.Arithmetic.Iteration
public import Foundation.FirstOrder.Arithmetic.Exponential.Exp
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Packed row lookup uses the same bit order and stride as the literal
table. The arithmetic uses division by a power of two for the shift. -/
def rowDef (table : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “d q r. ∃ bit, !remDef bit r 2 ∧ ∃ p,
    !expDef p (11 * (2 * q + bit)) ∧ ∃ a, !divDef a ↑table p ∧ !remDef d a 2048”

/-- Freeze a configuration once its state is outside the working states,
so arithmetic iteration is total. -/
def tickDef (limit table : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “after before. ∃ q l r, !pair₃Def before q l r ∧
    ((¬q < ↑limit ∧ after = before) ∨
      (q < ↑limit ∧ ∃ d, !(rowDef table) d q r ∧
        ∃ n w, !divDef n d 4 ∧ ∃ half, !divDef half d 2 ∧ !remDef w half 2 ∧
        ∃ dir rt, !remDef dir d 2 ∧ !divDef rt r 2 ∧
          ((dir = 1 ∧ !pair₃Def after n (2 * l + w) rt) ∨
           (dir = 0 ∧ ∃ lt v, !divDef lt l 2 ∧ !remDef v l 2 ∧
             !pair₃Def after n lt (4 * rt + 2 * w + v)))))”

def clockBlueprint (limit table : Nat) : PR.Blueprint 1 :=
  iterationBlueprint (tickDef limit table)

def haltsDef (limit table : Nat) : 𝚺ᴬ₁.Semisentence 0 :=
  .mkSigma “∃ time q l r out, !((clockBlueprint limit table).resultDef) out time 0 ∧
    !pair₃Def out q l r ∧ ¬q < ↑limit”

section Semantics

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def encode (state left right : M) : M := ⟪state,left,right⟫

theorem encode_projections (code : M) : encode (π₁ code) (π₁ (π₂ code)) (π₂ (π₂ code)) = code := by
  simp [encode]

noncomputable def divIn (a b : M) : M := a / b
noncomputable def remIn (a b : M) : M := a % b

noncomputable def digit (table : Nat) (state right : M) : M :=
  remIn (divIn (table : M) (Exp.exp (11 * (2 * state + remIn right 2)))) 2048

theorem rowDef_eval (table : Nat) (d q r : M) :
    (rowDef table).val.Evalb ![d,q,r] ↔ d = digit table q r := by
  simp [rowDef,digit,divIn,remIn,rem_defined.iff,exp_defined_deltaZero.iff,div_defined.iff,numeral_eq_natCast]

noncomputable def tick (limit table : Nat) (code : M) : M := by
  classical
  let q := π₁ code
  let l := π₁ (π₂ code)
  let r := π₂ (π₂ code)
  let d := digit table q r
  let n := divIn d 4
  let w := remIn (divIn d 2) 2
  let rt := divIn r 2
  exact if q < (limit : M) then
    if remIn d 2 = 1 then encode n (2*l+w) rt
    else encode n (divIn l 2) (4*rt+2*w+remIn l 2)
  else code

theorem tickDef_eval (limit table : Nat) (after before : M) :
    (tickDef limit table).val.Evalb ![after,before] ↔ after = tick limit table before := by
  classical
  have unpacked : (tickDef limit table).val.Evalb ![after,before] ↔
      ∃ q l r, before = encode q l r ∧
        ((¬q < (limit : M) ∧ after = before) ∨
        (q < (limit : M) ∧
          let d := digit table q r
          (d % 2 = 1 ∧ after = encode (d/4) (2*l+d/2%2) (r/2)) ∨
          (d % 2 = 0 ∧ after = encode (d/4) (l/2) (4*(r/2)+2*(d/2%2)+l%2)))) := by
    simp [tickDef,encode,rowDef_eval,pair₃_defined.iff,div_defined.iff,rem_defined.iff,numeral_eq_natCast,add_assoc]
  rw [unpacked]
  constructor
  · rintro ⟨q,l,r,rfl,closed | ⟨working,move⟩⟩
    · exact closed.2.trans (by simp [tick,divIn,remIn,encode,closed.1])
    · rcases move with ⟨direction,eq⟩ | ⟨direction,eq⟩
      · simpa [tick,divIn,remIn,encode,working,direction] using eq
      · simpa [tick,divIn,remIn,encode,working,direction] using eq
  · rintro rfl
    let q := π₁ before
    let l := π₁ (π₂ before)
    let r := π₂ (π₂ before)
    refine ⟨q,l,r,(encode_projections before).symm,?_⟩
    by_cases working : q < (limit : M)
    · refine Or.inr ⟨working,?_⟩
      rcases mod_two (digit table q r) with low | high
      · exact Or.inr ⟨low,by simp [tick,divIn,remIn,q,l,r,working,low]⟩
      · exact Or.inl ⟨high,by simp [tick,divIn,remIn,q,l,r,working,high]⟩
    · exact Or.inl ⟨working,by simp [tick,divIn,remIn,q,working]⟩

noncomputable def clockConstruction (limit table : Nat) :
    PR.Construction M (clockBlueprint limit table) :=
  iterationConstruction (tickDef limit table) (tick limit table) (tickDef_eval limit table)

noncomputable def clock (limit table : Nat) (n start : M) : M :=
  (clockConstruction limit table).result ![start] n

theorem clock_eval (limit table : Nat) (out time start : M) :
    (clockBlueprint limit table).resultDef.val.Evalb ![out,time,start] ↔
      out = clock limit table time start := by
  simp only [(clockConstruction limit table).result_defined_iff,Matrix.cons_val_zero,
    Matrix.cons_val_succ,clock]
  rfl

theorem clock_eval_vector (limit table : Nat) (args : Fin 3 → M) :
    (clockBlueprint limit table).resultDef.val.Evalb args ↔
      args 0 = clock limit table (args 1) (args 2) := by
  simpa only [← Matrix.fun_eq_vec_three args] using
    clock_eval limit table (args 0) (args 1) (args 2)

@[simp] theorem clock_zero (limit table : Nat) (start : M) : clock limit table 0 start = start := by
  unfold clock
  rw [PR.Construction.result_zero]
  rfl

@[simp] theorem clock_succ (limit table : Nat) (n start : M) :
    clock limit table (n+1) start = tick limit table (clock limit table n start) := by
  unfold clock
  rw [PR.Construction.result_succ]
  rfl

theorem clock_one (limit table : Nat) (start : M) :
    clock limit table 1 start = tick limit table start := by
  simpa only [zero_add,clock_zero] using clock_succ limit table (0 : M) start

@[definability] instance clock_definable (limit table : Nat) : 𝚺ᴬ₁-Function₂ (clock (M := M) limit table) := by
  have defined : 𝚺ᴬ₁-Function₂ (clock (M := M) limit table) via (clockBlueprint limit table).resultDef := by
    refine .mk fun v => ?_
    rw [Matrix.fun_eq_vec_three v]
    exact clock_eval limit table _ _ _
  exact defined.to_definable

theorem clock_add (limit table : Nat) (m n start : M) :
    clock limit table (m+n) start = clock limit table n (clock limit table m start) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => simp
  | succ n ih => rw [← add_assoc,clock_succ,clock_succ,ih]
  | hP => definability

theorem haltsDef_eval (limit table : Nat) :
    (haltsDef limit table).val.Evalb (![] : Fin 0 → M) ↔
      ∃ time : M, ¬π₁ (clock limit table time 0) < (limit : M) := by
  have semantics : (haltsDef limit table).val.Evalb (![] : Fin 0 → M) ↔
      ∃ time q l r : M, clock limit table time 0 = encode q l r ∧ ¬q < (limit : M) := by
    simp only [haltsDef,Bounding.HierarchySymbol.Semiformula.val_mkSigma,Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and,LogicalConnective.Prop.and_eq,Semiformula.eval_rew,
      Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton,
      numeral_eq_natCast,clock_eval,pair₃_defined.iff]
    simp only [clock_eval_vector,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
      Semiterm.val_bvar,numeral_eq_natCast]
    simp [encode,Semiformula.Operator.val,Semiformula.Operator.lt_def,numeral_eq_natCast,
      -not_lt,-exists_and_left,-exists_and_right]
  rw [semantics]
  constructor
  · rintro ⟨time,q,l,r,e,h⟩
    exact ⟨time,by simpa [e,encode] using h⟩
  · rintro ⟨time,h⟩
    exact ⟨time,_,_,_,(encode_projections _).symm,h⟩

end Semantics
end PalomarI3380.ArithmeticMachine
