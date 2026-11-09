module

public import PA211Statement
public import PA211PA.TwoSidedIndependence

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace PA211.Palomar

abbrev interpretation (M : Type) [ORingStructure M] : Arithmetic M :=
  ⟨0, 1, (· + ·), (· * ·), (· < ·)⟩

abbrev Arithmetic.asORing (A : Arithmetic M) : ORingStructure M where
  toZero := ⟨A.zero⟩
  toOne := ⟨A.one⟩
  toAdd := ⟨A.add⟩
  toMul := ⟨A.mul⟩
  toLT := ⟨A.lt⟩

def Term.toFoundation : Term ξ n → ArithmeticSemiterm ξ n
  | .bound i => .bvar i
  | .param x => .fvar x
  | .zero => .func .zero Fin.elim0
  | .one => .func .one Fin.elim0
  | .add t u => .func .add ![t.toFoundation, u.toFoundation]
  | .mul t u => .func .mul ![t.toFoundation, u.toFoundation]

def Formula.toFoundation : {n : Nat} → Formula ξ n → ArithmeticSemiformula ξ n
  | _, .top => .verum
  | _, .bot => .falsum
  | _, .eq t u => .rel .eq ![t.toFoundation, u.toFoundation]
  | _, .ne t u => .nrel .eq ![t.toFoundation, u.toFoundation]
  | _, .lt t u => .rel .lt ![t.toFoundation, u.toFoundation]
  | _, .nlt t u => .nrel .lt ![t.toFoundation, u.toFoundation]
  | _, .and p q => .and p.toFoundation q.toFoundation
  | _, .or p q => .or p.toFoundation q.toFoundation
  | _, .all p => .all p.toFoundation
  | _, .ex p => .exs p.toFoundation

def Term.ofFoundation : ArithmeticSemiterm ξ n → Term ξ n
  | .bvar i => .bound i
  | .fvar x => .param x
  | .func .zero _ => .zero
  | .func .one _ => .one
  | .func .add v => .add (ofFoundation (v 0)) (ofFoundation (v 1))
  | .func .mul v => .mul (ofFoundation (v 0)) (ofFoundation (v 1))

def Formula.ofFoundation : {n : Nat} → ArithmeticSemiformula ξ n → Formula ξ n
  | _, .verum => .top
  | _, .falsum => .bot
  | _, .rel .eq v => .eq (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | _, .nrel .eq v => .ne (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | _, .rel .lt v => .lt (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | _, .nrel .lt v => .nlt (Term.ofFoundation (v 0)) (Term.ofFoundation (v 1))
  | _, .and p q => .and (ofFoundation p) (ofFoundation q)
  | _, .or p q => .or (ofFoundation p) (ofFoundation q)
  | _, .all p => .all (ofFoundation p)
  | _, .exs p => .ex (ofFoundation p)

@[simp] theorem Term.to_ofFoundation (t : ArithmeticSemiterm ξ n) :
    (Term.ofFoundation t).toFoundation = t := by
  induction t with
  | bvar | fvar => rfl
  | func g v ih =>
    cases g <;> simp only [Term.ofFoundation, Term.toFoundation, ih] <;>
      congr 1 <;> funext i <;> fin_cases i <;> rfl

@[simp] theorem Formula.to_ofFoundation (p : ArithmeticSemiformula ξ n) :
    (Formula.ofFoundation p).toFoundation = p := by
  induction p with
  | rel r v | nrel r v =>
    cases r <;> simp only [Formula.ofFoundation, Formula.toFoundation, Term.to_ofFoundation] <;>
      congr 1 <;> funext i <;> fin_cases i <;> rfl
  | _ => simp_all only [Formula.ofFoundation, Formula.toFoundation]

@[simp] theorem Term.eval_toFoundation (t : Term ξ n) (b : Fin n → M) (f : ξ → M)
    [ORingStructure M] : t.toFoundation.val b f = t.eval (interpretation M) b f := by
  induction t <;> simp_all [Term.toFoundation, Term.eval] <;> rfl

@[simp] theorem Formula.eval_toFoundation (p : Formula ξ n) (b : Fin n → M) (f : ξ → M)
    [ORingStructure M] : p.toFoundation.Eval b f ↔ p.eval (interpretation M) f b := by
  induction p with
  | top | bot => rfl
  | eq | ne | lt | nlt =>
    simp [Formula.toFoundation, Formula.eval]
    rfl
  | and p q hp hq =>
    change (p.toFoundation.Eval b f ∧ q.toFoundation.Eval b f) ↔ _
    rw [Formula.eval, hp, hq]
  | or p q hp hq =>
    change (p.toFoundation.Eval b f ∨ q.toFoundation.Eval b f) ↔ _
    rw [Formula.eval, hp, hq]
  | all p hp =>
    change (∀ x, p.toFoundation.Eval (Fin.cons x b) f) ↔ _
    simp only [Formula.eval, hp]
  | ex p hp =>
    change (∃ x, p.toFoundation.Eval (Fin.cons x b) f) ↔ _
    simp only [Formula.eval, hp]

theorem isPA_iff (M : Type) [ORingStructure M] :
    IsPA (interpretation M) ↔ M↓[ℒₒᵣ] ⊧* Peano := by
  classical
  have induction_iff (p : ArithmeticSemiformula Nat 1) :
      M↓[ℒₒᵣ] ⊧ (succInd p).univCl ↔
        ∀ (f : Nat → M), p.Eval ![0] f →
          (∀ x, p.Eval ![x] f → p.Eval ![x + 1] f) → ∀ x, p.Eval ![x] f := by
    simp [Semiformula.eval_univCl, succInd, models_iff, Semiformula.eval_substs]
  constructor
  · intro h
    apply models_theory_iff.mpr
    intro p hp
    rcases hp with hp | ⟨q, _, rfl⟩
    · cases hp with
      | equal p hp => exact Theory.models M (𝗘𝗤 ℒₒᵣ) hp
      | addZero => simpa [PeanoMinus.Axiom.addZero, models_iff] using h.addZero
      | addAssoc => simpa [PeanoMinus.Axiom.addAssoc, models_iff] using h.addAssoc
      | addComm => simpa [PeanoMinus.Axiom.addComm, models_iff] using h.addComm
      | addEqOfLt => simpa [PeanoMinus.Axiom.addEqOfLt, models_iff, Semiformula.eval_bexsLTSucc] using h.addEqOfLt
      | zeroLe => simpa [PeanoMinus.Axiom.zeroLe, models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT] using h.zeroLe
      | zeroLtOne => simpa [PeanoMinus.Axiom.zeroLtOne, models_iff] using h.zeroLtOne
      | oneLeOfZeroLt => simpa [PeanoMinus.Axiom.oneLeOfZeroLt, models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT] using h.oneLeOfZeroLt
      | addLtAdd => simpa [PeanoMinus.Axiom.addLtAdd, models_iff] using h.addLtAdd
      | mulZero => simpa [PeanoMinus.Axiom.mulZero, models_iff] using h.mulZero
      | mulOne => simpa [PeanoMinus.Axiom.mulOne, models_iff] using h.mulOne
      | mulAssoc => simpa [PeanoMinus.Axiom.mulAssoc, models_iff] using h.mulAssoc
      | mulComm => simpa [PeanoMinus.Axiom.mulComm, models_iff] using h.mulComm
      | mulLtMul => simpa [PeanoMinus.Axiom.mulLtMul, models_iff] using h.mulLtMul
      | distr => simpa [PeanoMinus.Axiom.distr, models_iff] using h.distr
      | ltIrrefl => simpa [PeanoMinus.Axiom.ltIrrefl, models_iff] using h.ltIrrefl
      | ltTrans => simpa [PeanoMinus.Axiom.ltTrans, models_iff] using h.ltTrans
      | ltTri => simpa [PeanoMinus.Axiom.ltTri, models_iff] using h.ltTri
    · apply (induction_iff q).mpr
      simpa only [← Formula.eval_toFoundation, Formula.to_ofFoundation] using
        h.induction (Formula.ofFoundation q)
  · intro h
    have ax {p : ArithmeticSentence} (hp : PeanoMinus p) : M↓[ℒₒᵣ] ⊧ p :=
      models_theory_iff.mp h p (Or.inl hp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ax .addZero
    · simpa [PeanoMinus.Axiom.addAssoc, models_iff] using ax .addAssoc
    · simpa [PeanoMinus.Axiom.addComm, models_iff] using ax .addComm
    · simpa [PeanoMinus.Axiom.addEqOfLt, models_iff, Semiformula.eval_bexsLTSucc] using ax .addEqOfLt
    · exact ax .zeroLe
    · exact ax .zeroLtOne
    · simpa [PeanoMinus.Axiom.oneLeOfZeroLt, models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT] using ax .oneLeOfZeroLt
    · simpa [PeanoMinus.Axiom.addLtAdd, models_iff] using ax .addLtAdd
    · exact ax .mulZero
    · exact ax .mulOne
    · simpa [PeanoMinus.Axiom.mulAssoc, models_iff] using ax .mulAssoc
    · simpa [PeanoMinus.Axiom.mulComm, models_iff] using ax .mulComm
    · simpa [PeanoMinus.Axiom.mulLtMul, models_iff] using ax .mulLtMul
    · simpa [PeanoMinus.Axiom.distr, models_iff] using ax .distr
    · exact ax .ltIrrefl
    · simpa [PeanoMinus.Axiom.ltTrans, models_iff] using ax .ltTrans
    · simpa [PeanoMinus.Axiom.ltTri, models_iff] using ax .ltTri
    · intro p
      have hp := models_theory_iff.mp h _ (Or.inr ⟨p.toFoundation, Set.mem_univ p.toFoundation, rfl⟩)
      simpa only [Formula.eval_toFoundation] using (induction_iff p.toFoundation).mp hp

section Machine
open PA211.UserCandidate

theorem transition_eq : transition = Dense.machine := rfl

private theorem trim_eq (l : List Bool) : trim l = PA215.Zip.trim l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [trim, PA215.Zip.trim_cons, ih]

private def toZip (c : Configuration) : PA215.Zip.Conf := ⟨c.state, c.left, c.right⟩

private theorem toZip_config (q : Nat) (l r : List Bool) :
    toZip (config q l r) = PA215.Zip.zc q l r := by
  simp [toZip, config, PA215.Zip.zc, trim_eq]

private theorem toZip_step (c : Configuration) :
    (step c).map toZip = PA215.Zip.step Dense.machine (toZip c) := by
  rcases c with ⟨q, l, r⟩
  simp only [step, PA215.Zip.step, toZip, transition_eq]
  cases Dense.machine q (r.headD false) with
  | none => rfl
  | some action =>
    rcases action with ⟨w, d, q'⟩
    cases d <;> simp [toZip_config, PA215.Zip.zl]

private theorem toZip_run (n : Nat) (c : Configuration) :
    (run n c).map toZip = PA215.Zip.run Dense.machine n (toZip c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [PA215.Zip.run, ← toZip_step, run]
    cases step c <;> simp [ih]

theorem halts_iff :
    Halts ↔ PA215.Zip.Halts Dense.machine (PA215.Zip.zc 0 [] []) := by
  constructor
  · rintro ⟨n, c, hr, hs⟩
    refine ⟨toZip c, ⟨n, ?_⟩, ?_⟩
    · rw [← toZip_config, ← toZip_run, hr]; rfl
    · rw [← toZip_step, hs]; rfl
  · rintro ⟨z, ⟨n, hr⟩, hs⟩
    rw [← toZip_config, ← toZip_run] at hr
    cases hc : run n (config 0 [] []) with
    | none => simp [hc] at hr
    | some c =>
      have hz : toZip c = z := by simpa [hc] using hr
      rw [← hz, ← toZip_step] at hs
      exact ⟨n, c, hc, by simpa using hs⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem literal_counts : workingStates.length = 211 ∧ rows.length = 422 := by
  decide +kernel

end Machine

section Coding
open scoped FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]

@[simp] private theorem numeral_eq_cast (n : Nat) : numeral n = (n : V) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [numeral]
  | one => simp [numeral]
  | more n _ ih => simp [numeral, Nat.cast_succ, ih]

@[simp] private theorem divides_iff (a b : V) : divides a b ↔ a ∣ b := by
  simpa only [divides, not_lt] using (dvd_iff_bounded (a := a) (b := b)).symm

@[simp] private theorem quotient_iff (q a b : V) : quotient q a b ↔ q = a / b := by
  simpa only [quotient, not_lt] using (div_graph (a := a) (b := b) (c := q)).symm

@[simp] private theorem difference_iff (r a b : V) : difference r a b ↔ r = a - b := by
  simpa only [difference, not_lt] using (sub_eq_iff (a := a) (b := b) (c := r)).symm

@[simp] private theorem remainder_iff (r a b : V) : remainder r a b ↔ r = a % b := by
  simpa only [remainder, not_lt, quotient_iff, difference_iff] using (rem_graph r a b).symm

@[simp] private theorem digit_iff (r b a : V) : digit r b a ↔ r = ext b a := by
  simpa only [digit, not_lt, quotient_iff, remainder_iff] using (ext_graph r b a).symm

@[simp] private theorem powerOfTwo_iff (a : V) : powerOfTwo a ↔ Pow2 a := by
  simp only [powerOfTwo, Pow2, not_lt, divides_iff, one_add_one_eq_two]

@[simp] private theorem bitAt_iff (p a : V) : bitAt p a ↔ LenBit p a := by
  simp [bitAt, LenBit, one_add_one_eq_two]

@[simp] private theorem squareRoot_iff (r a : V) : squareRoot r a ↔ r = √a := by
  simpa only [squareRoot, square, not_lt] using (sqrt_graph (a := a) (b := r)).symm

@[simp] private theorem squaringMask_iff (m : V) : squaringMask m ↔ SPPow2 m := by
  simp [squaringMask, SPPow2, square, sq, one_add_one_eq_two]

@[simp] private theorem digitPlace_iff (p : V) : digitPlace p ↔ PPow2 p := by
  simp only [digitPlace, PPow2, powerOfTwo_iff, squaringMask_iff, bitAt_iff, one_add_one_eq_two]

@[simp] private theorem twoTo_iff (x y : V) : twoTo x y ↔ Exponential x y := by
  rw [Exponential.graph_iff]
  simp only [twoTo, not_lt, digit_iff, numeral_eq_cast, digitPlace_iff,
    one_add_one_eq_two, square, sq, pow_four, Exponential.Seqₛ.iff, Nat.cast_ofNat]

@[simp] private theorem contains_iff (i s : V) : contains i s ↔ i ∈ s := by
  change contains i s ↔ LenBit (Exp.exp i) s
  simp only [contains, not_lt, twoTo_iff, bitAt_iff, ← exponential_graph]
  constructor
  · rintro ⟨p, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, h.le, rfl, h⟩

@[simp] private theorem pairCode_iff (c a b : V) : pairCode c a b ↔ c = ⟪a, b⟫ := by
  simpa only [pairCode, square, not_lt] using (pair_graph (a := a) (b := b) (c := c)).symm

@[simp] private theorem tripleCode_iff (c a b d : V) :
    tripleCode c a b d ↔ c = ⟪a, b, d⟫ := by
  simp [tripleCode]

@[simp] private theorem unconsCode_iff (v a b : V) :
    unconsCode v a b ↔ a = fstIdx v ∧ b = sndIdx v := by
  rcases nil_or_adjoin v with rfl | ⟨x, y, rfl⟩
  · simp [unconsCode, fstIdx, sndIdx, pi₁_zero, pi₂_zero]
  · rw [fstIdx_adjoin, sndIdx_adjoin]
    simp [unconsCode, adjoin_def, eq_comm]

private theorem predecessor_lt (w i z : V) : ⟪sndIdx w, i, z⟫ < ⟪w, i + 1, z⟫ := by
  apply lt_of_le_of_lt (pair_le_pair_left (sndIdx_le_self w) _)
  exact pair_lt_pair_right _ (pair_lt_pair_left (by simp) _)

private theorem graph_iff_certificate (c : V) :
    Nth.Graph c ↔ ∃ s : V, c ∈ s ∧ ∀ d ∈ s, Nth.Phi {e | e ∈ s} d := by
  constructor
  · intro hc
    have hdef : 𝚺ᴬ₁-Predicate (fun d : V => d ≤ c ∧ Nth.Graph d) := by
      apply Bounding.HierarchySymbol.Definable.and
      · definability
      · exact Nth.graph_definable
    obtain ⟨s, hs⟩ := (finite_comprehension₁! hdef
      ⟨c + 1, fun d hd => lt_succ_iff_le.mpr hd.1⟩).exists
    refine ⟨s, (hs c).mpr ⟨le_rfl, hc⟩, ?_⟩
    intro d hd
    obtain ⟨hle, hg⟩ := (hs d).mp hd
    rcases Nth.graph_case.mp hg with hzero | ⟨w, i, z, rfl, hpred⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨w, i, z, rfl, (hs _).mpr ⟨(predecessor_lt w i z).le.trans hle, hpred⟩⟩
  · rintro ⟨s, hc, hs⟩
    have hdef : 𝚺ᴬ₁-Predicate (fun d : V => d ∈ s → Nth.Graph d) := by
      apply Bounding.HierarchySymbol.Definable.imp
      · definability
      · exact Nth.graph_definable
    have hall : ∀ d : V, d ∈ s → Nth.Graph d := by
      apply InductionOnHierarchy.order_induction 𝚺 1 hdef
      intro d ih hd
      apply Nth.graph_case.mpr
      rcases hs d hd with hzero | ⟨w, i, z, rfl, hpred⟩
      · exact Or.inl hzero
      · exact Or.inr ⟨w, i, z, rfl, ih _ (predecessor_lt w i z) hpred⟩
    exact hall c hc

@[simp] private theorem nthCode_iff (v i x : V) : nthCode v i x ↔ nth v i = x := by
  rw [← (show Nth.Graph ⟪v, i, x⟫ ↔ nth v i = x from
    ⟨nth_eq_of_graph, fun h => h ▸ nth_graph v i⟩), graph_iff_certificate]
  simp [nthCode, Nth.Phi, and_assoc]

end Coding

section Endpoint

open PA211.UserCandidate PA211.UserCandidate.PA
open scoped FFL.FirstOrder.Bounding

def fromRow (p : WorkingState × Bool) : Nat × Bool × Bool × Bool × Nat :=
  let a := row p.1 p.2
  (p.1.val, p.2, a.write, a.right, StepFormula.controlCode a.next)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem exact_rows_eq : ExactHaltingFormula.rows.map fromRow = rows := by
  decide +kernel

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]

omit [V↓[ℒₒᵣ] ⊧* Peano] in
private theorem disjoin_eval (rs : List (WorkingState × Bool)) (e : Fin 6 → V) :
    (V ⊧/e (StepFormula.disjoin rs)) ↔
      ∃ p ∈ rs, V ⊧/e (StepFormula.rowFormula p.1 p.2) := by
  induction rs with
  | nil => simp [StepFormula.disjoin]
  | cons p rs ih => simp [StepFormula.disjoin, ih]

private theorem exact_step_iff (q l r q' l' r' : V) :
    (V ⊧/![q,l,r,q',l',r'] ExactHaltingFormula.formula) ↔ stepCode q l r q' l' r' := by
  rw [ExactHaltingFormula.formula, disjoin_eval, stepCode, ← exact_rows_eq]
  simp only [List.mem_map]
  have hrow (p : WorkingState × Bool) :
      (V ⊧/![q,l,r,q',l',r'] (StepFormula.rowFormula p.1 p.2)) ↔
        rowCode (fromRow p) q l r q' l' r' := by
    rcases p with ⟨s,b⟩
    cases hd : (row s b).right <;> simp [StepFormula.rowFormula, rowCode, fromRow, hd, numeral_eq_natCast]
    intro _ _
    constructor
    · rintro ⟨t, u, ⟨hl, hr, rfl, ht⟩ | ⟨hl, hr, rfl, ht⟩⟩
      · exact ⟨t, Or.inl ⟨hl, hr, ht⟩⟩
      · exact ⟨t, Or.inr ⟨hl, hr, ht⟩⟩
    · rintro ⟨t, ⟨hl, hr, ht⟩ | ⟨hl, hr, ht⟩⟩
      · exact ⟨t, l', Or.inl ⟨hl, hr, rfl, ht⟩⟩
      · exact ⟨t, l', Or.inr ⟨hl, hr, rfl, ht⟩⟩
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨fromRow p, ⟨p, hp, rfl⟩, (hrow p).mp h⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, h⟩
    exact ⟨p, hp, (hrow p).mpr h⟩

private theorem trace_iff :
    (V ⊧/![] ExactHaltingFormula.traceSentence) ↔ traceCode (M := V) := by
  have he (b : Fin 6 → V) :
      (V ⊧/b ExactHaltingFormula.formula) ↔
        stepCode (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
    have hb : b = ![b 0, b 1, b 2, b 3, b 4, b 5] := by
      simp [funext_iff, Fin.forall_fin_succ]
    conv_lhs => rw [hb]
    exact exact_step_iff _ _ _ _ _ _
  simp [ExactHaltingFormula.traceSentence, ExactHaltingFormula.trace, traceCode,
    nth_defined.df, he, numeral_eq_natCast, Nat.cast_ofNat, eq_comm]

/-- Agreement with the existing exact arithmetic sentence in every model of PA. -/
theorem exact_sentence_iff :
    nonhaltingSentence V (interpretation V) ↔ V↓[ℒₒᵣ] ⊧ ExactHaltingFormula.nonhaltingSentence := by
  change (¬ traceCode (M := V)) ↔ _
  simpa [models_iff, ExactHaltingFormula.nonhaltingSentence] using
    not_congr (trace_iff (V := V)).symm

end Endpoint

/-- The semantic presentation realizes a sentence that translates back to
Foundation's exact syntax. The PA model restriction includes nonstandard models. -/
theorem exact_formula_representation :
    ∃ p : Sentence, p.toFoundation = PA211.UserCandidate.PA.ExactHaltingFormula.nonhaltingSentence ∧
      ∀ (V : Type) (A : Arithmetic V), IsPA A →
        (p.eval A Empty.elim Fin.elim0 ↔ nonhaltingSentence V A) := by
  let φ := PA211.UserCandidate.PA.ExactHaltingFormula.nonhaltingSentence
  refine ⟨Formula.ofFoundation φ, Formula.to_ofFoundation φ, ?_⟩
  intro V A hA
  let _ : ORingStructure V := A.asORing
  let _ : V↓[ℒₒᵣ] ⊧* Peano := (isPA_iff V).mp hA
  have h := Formula.eval_toFoundation (Formula.ofFoundation φ) (Fin.elim0 : Fin 0 → V) Empty.elim
  rw [Formula.to_ofFoundation] at h
  exact h.symm.trans (exact_sentence_iff (V := V)).symm

/-- First-order soundness and completeness for the Challenge interpretation of PA. -/
theorem paProvable_iff (p : (V : Type) → Arithmetic V → Prop) (φ : ArithmeticSentence)
    (alignment : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano],
      p V (interpretation V) ↔ V↓[ℒₒᵣ] ⊧ φ) :
    PAProvable p ↔ Peano ⊢ φ := by
  constructor
  · intro h
    apply Arithmetic.complete.{0} Peano φ
    intro V _ hm
    exact (alignment V).mp (h V (interpretation V) ((isPA_iff V).mpr hm))
  · intro h V A hA
    let _ : ORingStructure V := A.asORing
    let _ : V↓[ℒₒᵣ] ⊧* Peano := (isPA_iff V).mp hA
    exact (alignment V).mpr (consequence_iff.mp (Theory.Proof.sound h) V inferInstance)

open PA211.UserCandidate.PA in
theorem nonhalting_provable_iff :
    PAProvable nonhaltingSentence ↔ theory ⊢ ExactHaltingFormula.nonhaltingSentence :=
  paProvable_iff _ _ (fun _ _ _ => exact_sentence_iff)

open PA211.UserCandidate.PA in
theorem negation_provable_iff :
    PAProvable (fun M A => ¬ nonhaltingSentence M A) ↔
      theory ⊢ ∼ExactHaltingFormula.nonhaltingSentence := by
  apply paProvable_iff
  intro V _ _
  simpa [models_iff] using not_congr (exact_sentence_iff (V := V))

theorem blank_nonhalting : workingStates.length = 211 ∧ rows.length = 422 ∧ ¬ Halts :=
  ⟨literal_counts.1, literal_counts.2,
    fun h => PA211.UserCandidate.PA.Independence.machine_nonhalting (halts_iff.mp h)⟩

theorem two_sided_independence :
    ¬ PAProvable nonhaltingSentence ∧
    ¬ PAProvable (fun M A => ¬ nonhaltingSentence M A) := by
  rw [nonhalting_provable_iff, negation_provable_iff]
  exact PA211.UserCandidate.PA.Independence.two_sided_independence

#print axioms transition_eq
#print axioms exact_rows_eq
#print axioms halts_iff
#print axioms exact_sentence_iff
#print axioms exact_formula_representation
#print axioms nonhalting_provable_iff
#print axioms negation_provable_iff
/-- info: 'PA211.Palomar.blank_nonhalting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blank_nonhalting
/-- info: 'PA211.Palomar.two_sided_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_sided_independence

end PA211.Palomar
