module
public import I0451.Logic.SourceAxiomForms

/-! Give each parameter of a set-language formula a distinct numeric
label before using it in the AX collection schema. Odd labels above
two represent free parameters. Even labels above three bind variables. -/
@[expose] public section
namespace I0451.Logic.NamedFormula

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Arithmetization I0451.Runtime

def parameterLabel (i : Nat) : Nat := 2*i+3
def binderLabel (d : Nat) : Nat := 2*d+4

def termName {n : Nat} (bound : Fin n → Nat) : SyntacticSemiterm ℒₛₑₜ n → Nat
  | .bvar i => bound i
  | .fvar i => parameterLabel i
  | .func r _ => nomatch r

def fromSet : {n : Nat} → SetTheorySemiproposition n → (Fin n → Nat) → Nat → NamedFormula
  | _, .verum, _, _ => .truth
  | _, .falsum, _, _ => .falsity
  | _, .rel .eq terms, b, _ => .equal (termName b (terms 0)) (termName b (terms 1))
  | _, .rel .mem terms, b, _ => .mem (termName b (terms 0)) (termName b (terms 1))
  | _, .nrel .eq terms, b, _ => (.equal (termName b (terms 0)) (termName b (terms 1)) : NamedFormula).not
  | _, .nrel .mem terms, b, _ => (.mem (termName b (terms 0)) (termName b (terms 1)) : NamedFormula).not
  | _, .and p q, b, d => (fromSet p b d).and (fromSet q b d)
  | _, .or p q, b, d => (fromSet p b d).or (fromSet q b d)
  | _, .all p, b, d => .all (binderLabel d) (fromSet p (binderLabel d :> b) (d+1))
  | _, .exs p, b, d => existsAt (binderLabel d) (fromSet p (binderLabel d :> b) (d+1))

variable {V : Type} [SetStructure V]

private theorem termName_eval {n : Nat} (b : Fin n → Nat) (s : Nat → V) (t : SyntacticSemiterm ℒₛₑₜ n) :
    s (termName b t) = t.val (s ∘ b) (s ∘ parameterLabel) := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func fn t => exact nomatch fn

private theorem extendBound {n : Nat} (b : Fin n → Nat) (s : Nat → V) {d : Nat}
    (before : ∀ i, b i < binderLabel d) (value : V) :
    (assign s (binderLabel d) value ∘ (binderLabel d :> b)) = value :> (s ∘ b) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [assign]
  | succ i =>
    have different := (before i).ne
    simp [assign,Function.comp_def,different]

private theorem extendFree (s : Nat → V) (d : Nat) (value : V) :
    (assign s (binderLabel d) value ∘ parameterLabel) = s ∘ parameterLabel := by
  funext i
  have unequal : parameterLabel i ≠ binderLabel d := by
    unfold parameterLabel binderLabel
    omega
  simp [assign,Function.comp_def,unequal]

private theorem raised {n : Nat} (d : Nat) (b : Fin n → Nat) (earlier : ∀ i, b i < binderLabel d)
    (i : Fin (n+1)) : (binderLabel d :> b) i < binderLabel (d+1) := by
  cases i using Fin.cases with
  | zero => simp [binderLabel]
  | succ i =>
    have hi := earlier i
    simp [binderLabel] at hi ⊢
    omega

private theorem termNames_eval {n : Nat} (b : Fin n → Nat) (s : Nat → V)
    (terms : Fin 2 → SyntacticSemiterm ℒₛₑₜ n) :
    Semiterm.val (s ∘ b) (s ∘ parameterLabel) ∘ terms =
      ![s (termName b (terms 0)),s (termName b (terms 1))] := by
  rw [Matrix.fun_eq_vec_two (Semiterm.val (s ∘ b) (s ∘ parameterLabel) ∘ terms)]
  simp only [Function.comp_apply, termName_eval]

theorem fromSet_eval {n : Nat} (p : SetTheorySemiproposition n) (b : Fin n → Nat) (d : Nat)
    (earlier : ∀ i, b i < binderLabel d) (s : Nat → V) :
    (fromSet p b d).eval s ↔ p.Eval (s ∘ b) (s ∘ parameterLabel) := by
  induction p using Semiformula.rec' generalizing d s with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r terms =>
    cases r <;> simp [fromSet, eval, Semiformula.eval_rel, termNames_eval]
  | hnrel r terms =>
    cases r <;> simp [fromSet, eval, Semiformula.eval_nrel, termNames_eval]
  | hand p q hp hq => simp [fromSet, hp b d earlier s, hq b d earlier s]
  | hor p q hp hq => simp [fromSet, hp b d earlier s, hq b d earlier s]
  | hall p ih =>
    simp only [fromSet,eval,Semiformula.eval_all]
    refine forall_congr' fun v => ?_
    rw [ih _ _ (raised d b earlier), extendBound b s earlier v, extendFree s d v]
  | hexs p ih =>
    simp only [fromSet,eval_existsAt,Semiformula.eval_ex]
    refine exists_congr fun v => ?_
    rw [ih _ _ (raised d b earlier), extendBound b s earlier v, extendFree s d v]

theorem label_lt_code {f : NamedFormula} {x : Nat} (appears : x ∈ f.labels) : x < f.code := by
  have pairBound (a b : Nat) := pair_ge a b
  induction f with
  | truth | falsity => simp [labels] at appears
  | mem a b | equal a b =>
    simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at appears
    simp only [code,modelTag,modelImp,cantor_nat_pair]
    have h := pairBound a b
    omega
  | all a b ih =>
    simp only [labels,List.mem_cons] at appears
    simp only [code,modelTag,modelImp,cantor_nat_pair]
    have h := pairBound a b.code
    have bound := appears.imp id ih
    omega
  | imp a b ihA ihB =>
    simp only [labels,List.mem_append] at appears
    simp only [code,modelImp,cantor_nat_pair]
    have h := pairBound a.code b.code
    have bounds := appears.imp ihA ihB
    omega

theorem wrapped_code_bound (f : NamedFormula) : 2 < (f.and .truth).code := by
  show 2 < modelImp ((f.imp (.truth : NamedFormula).not).code) 1
  simp only [modelImp,cantor_nat_pair]
  have h := pair_ge ((f.imp (.truth : NamedFormula).not).code) 1
  omega

theorem name_definable_relation (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) (A : V) :
    ∃ f : NamedFormula, ∃ s : Nat → V, s 2 = A ∧ 2 < f.code ∧
      ∀ x y : V, f.eval (assign (assign s 1 x) 2 y) ↔ R x y := by
  classical
  obtain ⟨φ, reads⟩ := defR
  let : Inhabited V := ⟨A⟩
  let params := φ.enumerateFVar
  let body : SetTheorySemiproposition 2 := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  let f := (fromSet body ![1,2] 0).and .truth
  let s (i : Nat) : V := if i = 2 then A else params ((i-3)/2)
  have related (x y : V) : f.eval (assign (assign s 1 x) 2 y) ↔ R x y := by
    let vals := assign (assign s 1 x) 2 y
    have bound : (fun i : Fin 2 => vals (![1,2] i)) = ![x,y] := by
      rw [Matrix.fun_eq_vec_two (fun i : Fin 2 => vals (![1,2] i))]
      rfl
    have free : vals ∘ parameterLabel = params := by
      funext i
      have one : parameterLabel i ≠ 1 := by unfold parameterLabel; omega
      have two : parameterLabel i ≠ 2 := by unfold parameterLabel; omega
      have step : (parameterLabel i - 3) / 2 = i := by unfold parameterLabel; omega
      simp [vals, s, assign, Function.comp_def, one, two, step]
    have guard (i : Fin 2) : (![1,2] : Fin 2 → Nat) i < binderLabel 0 := by
      have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> decide
    have nativeToSet := fromSet_eval body ![1,2] 0 guard vals
    change ((fromSet body ![1,2] 0).and NamedFormula.truth).eval vals ↔ R x y
    rw [NamedFormula.eval_and]
    simp only [NamedFormula.eval, and_true]
    rw [nativeToSet, free]
    change body.Eval (fun i : Fin 2 => vals (![1,2] i)) params ↔ _
    rw [bound]
    simpa [body, params, Semiformula.eval_rewriteMap] using reads.iff ![x,y]
  exact ⟨f,s,by simp [s],wrapped_code_bound _,related⟩

end I0451.Logic.NamedFormula
