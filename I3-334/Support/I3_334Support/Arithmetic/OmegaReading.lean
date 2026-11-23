module
public import I3_334Support.Arithmetic.TranslateFormula
public import I3_334Support.Logic.NameMap
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {X Y ξ : Type} {n : Nat}

private theorem mapNames_numeralAt (f : X → Y) (k : Nat) (a : Argument X) :
    (numeralAt k a).mapNames f = numeralAt k (a.mapNames f) :=
  mapNames_template _ _ _ _

private theorem map_threeArgs (f : X → Y) (a b c : Argument X) :
    (fun i => (threeArgs a b c i).mapNames f) = threeArgs (a.mapNames f) (b.mapNames f) (c.mapNames f) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

private theorem mapNames_additionAt (f : X → Y) (a b c : Argument X) :
    (additionAt a b c).mapNames f = additionAt (a.mapNames f) (b.mapNames f) (c.mapNames f) := by
  simp only [additionAt,mapNames_template,map_threeArgs]

private theorem mapNames_multiplicationAt (f : X → Y) (a b c : Argument X) :
    (multiplicationAt a b c).mapNames f = multiplicationAt (a.mapNames f) (b.mapNames f) (c.mapNames f) := by
  simp only [multiplicationAt,mapNames_template,map_threeArgs]

private theorem map_variable (f : X → Y) (i : Nat) :
    (Argument.variable i).mapNames f = .variable i := rfl

private theorem map_up (a : Argument X) (f : X → Y) : (a.up).mapNames f = (a.mapNames f).up :=
  Argument.mapNames_rename _ _ _

private theorem map_shifted {ι : Type} (f : X → Y) (args : ι → Argument X) :
    Argument.mapNames f ∘ Argument.up ∘ args = Argument.up ∘ Argument.mapNames f ∘ args :=
  funext fun i => map_up (args i) f

private theorem translateTerm_mapNames (t : ArithmeticSemiterm ξ n) (f : X → Y)
    (bound : Fin n → Argument X) (free : ξ → Argument X) (out : Argument X) :
    (translateTerm t bound free out).mapNames f =
      translateTerm t (Argument.mapNames f ∘ bound) (Argument.mapNames f ∘ free) (out.mapNames f) := by
  induction t generalizing bound free out with
  | bvar | fvar => rfl
  | func op vals ih =>
    cases op <;> simp only [translateTerm,mapNames_numeralAt,Formula.mapNames,ih,map_variable,
      map_shifted,Function.comp_apply,map_up,mapNames_additionAt,mapNames_multiplicationAt]

private theorem mapNames_atom (less : Bool) (v : Fin 2 → ArithmeticSemiterm ξ n)
    (f : X → Y) (bound : Fin n → Argument X) (free : ξ → Argument X) :
    (arithmeticAtom less v bound free).mapNames f =
      arithmeticAtom less v (Argument.mapNames f ∘ bound) (Argument.mapNames f ∘ free) := by
  cases less <;> simp only [arithmeticAtom,↓reduceIte,Bool.false_eq_true,Formula.mapNames,
    translateTerm_mapNames,map_shifted,Function.comp_apply,map_up,map_variable]

private theorem mapNames_boundUnderBinder (b : Fin n → Argument X) (f : X → Y) :
    Argument.mapNames f ∘ boundUnderBinder b = boundUnderBinder (Argument.mapNames f ∘ b) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simp only [Function.comp_apply,boundUnderBinder,Fin.cons_succ,map_up]

theorem translateFormula_mapNames (φ : ArithmeticSemiformula ξ n) (f : X → Y)
    (omega : Argument X) (bound : Fin n → Argument X) (free : ξ → Argument X) :
    (translateFormula φ omega bound free).mapNames f =
      translateFormula φ (omega.mapNames f) (Argument.mapNames f ∘ bound) (Argument.mapNames f ∘ free) := by
  induction φ generalizing omega free with
  | verum | falsum => rfl
  | rel r v | nrel r v =>
    cases r <;> simp only [translateFormula,mapNames_atom,neg,Formula.mapNames]
  | and p q ip iq | or p q ip iq =>
    simp only [translateFormula,Formula.mapNames,ip,iq]
  | all p ih | exs p ih =>
    simp only [translateFormula,Formula.mapNames,map_variable,ih,map_up,map_shifted,mapNames_boundUnderBinder,
      Function.comp_apply]

end PalomarI3380.Logic.Expanded

namespace PalomarI3380.Logic

open Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

def expandedArithmeticReading {V : Type} (φ : ArithmeticSentence) : Expanded.Formula V :=
  .ex (.and (applyTemplate (SetFormula.omegaSet 0) 1 (fun _ => .variable 0))
    (translateFormula φ (.variable 0) Fin.elim0 Empty.elim))

/-- Relativize an arithmetic sentence to the natural numbers of a
membership structure. The resulting source formula is parameter-free. -/
def readArithmetic (φ : ArithmeticSentence) : Logic.Formula :=
  (expandedArithmeticReading (V := Empty) φ).lower Empty.elim 0

theorem expandedArithmeticReading_scope {V : Type} (φ : ArithmeticSentence) :
    Expanded.Bound (expandedArithmeticReading (V := V) φ) 0 :=
  ⟨applyTemplate_scope _ (SetFormula.scope_omega (Nat.zero_lt_succ 0)) _
      (fun _ _ => Nat.zero_lt_succ _),
    translateFormula_scope φ (Nat.zero_lt_succ _) (fun i => i.elim0) (fun i => i.elim)⟩

theorem readArithmetic_closed (φ : ArithmeticSentence) : Closed (readArithmetic φ) :=
  Expanded.lower_scope _ _ (m := 0) (expandedArithmeticReading_scope φ) (fun impossible => impossible.elim)

private theorem expandedArithmeticReading_map {V : Type} (φ : ArithmeticSentence) :
    (expandedArithmeticReading (V := Empty) φ).mapNames (Empty.elim : Empty → V) =
      expandedArithmeticReading φ := by
  simp only [expandedArithmeticReading,Formula.mapNames,mapNames_template,Argument.mapNames,translateFormula_mapNames]
  congr 1
  congr 1
  congr 1
  · funext i
    exact i.elim0
  · funext i
    exact i.elim

theorem readArithmetic_eval {V : Type} {E : V → V → Prop}
    {h : ClassAxioms E (fun _ _ => False)} {inhabited : Nonempty V} (D : OmegaDomain h inhabited)
    (φ : ArithmeticSentence) (env : Nat → V) :
    Logic.eval E (readArithmetic φ) env ↔ φ.Evalb (![] : Fin 0 → D.Points) := by
  let syntax' : Expanded.Formula V := expandedArithmeticReading φ
  have expanded := expandedArithmeticReading_map (V := V) φ
  have pure : syntax'.names = [] := by
    have noNames : (expandedArithmeticReading (V := Empty) φ).names = [] := by
      cases h : (expandedArithmeticReading (V := Empty) φ).names with
      | nil => rfl
      | cons x xs => exact x.elim
    rw [show syntax' = expandedArithmeticReading φ from rfl,← expanded,mapNames_names,noNames,List.map_nil]
  have lowered : syntax'.lower (fun _ => 0) 0 = readArithmetic φ := by
    rw [show syntax' = expandedArithmeticReading φ from rfl,← expanded,mapNames_lower]
    congr 1
    funext x
    exact x.elim
  rw [← lowered]
  refine (Expanded.lower_eval E (fun _ => 0) syntax' (expandedArithmeticReading_scope φ)
    env env (fun _ h => by omega) (fun v hm => by rw [pure] at hm; exact (List.not_mem_nil hm).elim)).trans ?_
  have meaning (w : V) : Expanded.eval E (fun _ _ => False)
      (applyTemplate (SetFormula.omegaSet 0) 1 (fun _ => .variable 0)) (pushValue env w) ↔
      Internal.Omega E w :=
    (applyTemplate_eval _ (SetFormula.scope_omega (Nat.zero_lt_succ 0)) _ _).trans
      (SetFormula.holds_omegaSet (Nat.zero_lt_succ 0))
  have arithmetic : Expanded.eval E (fun _ _ => False)
      (translateFormula φ (.variable 0) Fin.elim0 Empty.elim) (pushValue env D.omega) ↔
      φ.Evalb (![] : Fin 0 → D.Points) :=
    translateFormula_eval D φ (.variable 0) Fin.elim0 Empty.elim (pushValue env D.omega) ![] Empty.elim rfl (fun i => i.elim0) (fun i => i.elim)
  constructor
  · rintro ⟨w,omega,reads⟩
    have same := (h.context inhabited).omega_unique ((meaning _).mp omega) D.specification
    subst w
    exact arithmetic.mp reads
  · intro reads
    exact ⟨D.omega,(meaning _).mpr D.specification,arithmetic.mpr reads⟩

end PalomarI3380.Logic
