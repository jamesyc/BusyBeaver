module
public import I3_334Support.Arithmetic.GuardedArithmetic
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}

def variableIndex : Argument Empty → Nat
  | .variable i => i
  | .named x => x.elim

private theorem variableIndex_scope (arg : Argument Empty) {n : Nat} :
    arg.bound n → variableIndex arg < n := by cases arg with
    | «variable» => exact id
    | named x => exact x.elim

private theorem variableIndex_value (arg : Argument Empty) (env : Nat → V) :
    (arg.mapNames Empty.elim).value env = env (variableIndex arg) := by
  cases arg with
  | «variable» => rfl
  | named x => exact x.elim

/-- Parameter-free expanded syntax can be used in the ambient
separation and recursion interfaces. Its variables may range over
arithmetic codes and over arbitrary sets in the same formula. -/
def Formula.toClassRelation : Formula Empty → RelationFormula (ClassRelation E G)
  | .bot => .bot
  | .eq x y => .eq (variableIndex x) (variableIndex y)
  | .mem x y => .atom ClassRelation.member (variableIndex x) (variableIndex y)
  | .order x y => .atom ⟨G,⟨.order (.variable 0) (.variable 1),⟨by change 0 < 2; decide,by change 1 < 2; decide⟩,fun _ => Iff.rfl⟩⟩ (variableIndex x) (variableIndex y)
  | .and p q => .and p.toClassRelation q.toClassRelation
  | .or p q => .or p.toClassRelation q.toClassRelation
  | .imp p q => .imp p.toClassRelation q.toClassRelation
  | .all p => .all p.toClassRelation
  | .ex p => .ex p.toClassRelation

theorem Formula.toClassRelation_scope (φ : Formula Empty) {n : Nat} (scope : Bound φ n) :
    (φ.toClassRelation (E := E) (G := G)).Bound n := by
  induction φ generalizing n with
  | bot => trivial
  | eq x y | mem x y | order x y => exact ⟨variableIndex_scope x scope.1,variableIndex_scope y scope.2⟩
  | and p q pih qih | or p q pih qih | imp p q pih qih => exact ⟨pih scope.1,qih scope.2⟩
  | all p ih | ex p ih => exact ih scope

theorem Formula.toClassRelation_eval (φ : Formula Empty) (env : Nat → V) :
    RelationFormula.eval (ClassRelation.square E G) φ.toClassRelation env ↔
      eval E G (φ.mapNames Empty.elim) env := by
  induction φ generalizing env with
  | bot => rfl
  | eq x y =>
    change env (variableIndex x) = env (variableIndex y) ↔ _
    rw [← variableIndex_value x env,← variableIndex_value y env]
    rfl
  | mem x y =>
    change E (env (variableIndex x)) (env (variableIndex y)) ↔ _
    rw [← variableIndex_value x env,← variableIndex_value y env]
    rfl
  | order x y =>
    change G (env (variableIndex x)) (env (variableIndex y)) ↔ _
    rw [← variableIndex_value x env,← variableIndex_value y env]
    rfl
  | and p q pih qih => exact and_congr (pih env) (qih env)
  | or p q pih qih => exact or_congr (pih env) (qih env)
  | imp p q pih qih => exact imp_congr (pih env) (qih env)
  | all p ih => exact forall_congr' (fun x => ih (pushValue env x))
  | ex p ih => exact exists_congr (fun x => ih (pushValue env x))

def argumentsIn (ω : Nat) : (n : Nat) → (Fin n → Nat) → Formula Empty
  | 0, _ => .imp .bot .bot
  | n+1, arg => .and (.mem (.variable (arg 0)) (.variable ω)) (argumentsIn ω n (arg ∘ Fin.succ))

private theorem argumentsIn_scope (ω : Nat) (n : Nat) (arg : Fin n → Nat) {scope : Nat}
    (ho : ω < scope) (ha : ∀ i, arg i < scope) : Bound (argumentsIn ω n arg) scope := by
  induction n with
  | zero => exact ⟨trivial,trivial⟩
  | succ n ih => exact ⟨⟨ha 0,ho⟩,ih _ (fun i => ha i.succ)⟩

private theorem argumentsIn_eval (ω : Nat) (n : Nat) (arg : Fin n → Nat) (env : Nat → V) :
    eval E G ((argumentsIn ω n arg).mapNames Empty.elim) env ↔ ∀ i, E (env (arg i)) (env ω) := by
  induction n with
  | zero => exact ⟨fun _ i => i.elim0,fun _ h => h⟩
  | succ n ih =>
    change (E (env (arg 0)) (env ω) ∧
      eval E G ((argumentsIn ω n (arg ∘ Fin.succ)).mapNames Empty.elim) env) ↔ _
    rw [ih]
    exact ⟨fun ⟨head,tail⟩ i => Fin.cases head tail i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

/-- Embed an arithmetic predicate with the omega object and the
arguments selected by the surrounding set formula. -/
def arithmeticAt {n : Nat} (predicate : Semiformula ℒₒᵣ Empty n)
    (ω : Nat) (arg : Fin n → Nat) : Formula Empty :=
  .and (argumentsIn ω n arg)
    (translateFormula predicate (.variable ω) (fun i => .variable (arg i)) Empty.elim)

theorem arithmeticAt_scope {n scope ω : Nat} {arg : Fin n → Nat}
    (predicate : Semiformula ℒₒᵣ Empty n) (ho : ω < scope) (ha : ∀ i, arg i < scope) :
    Bound (arithmeticAt predicate ω arg) scope :=
  ⟨argumentsIn_scope ω n arg ho ha,translateFormula_scope predicate ho ha (fun i => i.elim)⟩

theorem arithmeticAt_eval {L : ClassAxioms E G} {inh : Nonempty V} (D : OmegaDomain L inh)
    {n ω : Nat} (predicate : Semiformula ℒₒᵣ Empty n) {arg : Fin n → Nat}
    {env : Nat → V} (omega : env ω = D.omega) :
    eval E G ((arithmeticAt predicate ω arg).mapNames Empty.elim) env ↔
      ∃ points : Fin n → D.Points, (∀ i, (points i).val = env (arg i)) ∧ predicate.Evalb points := by
  unfold arithmeticAt
  rw [Formula.mapNames,translateFormula_mapNames]
  have free : (Argument.mapNames (Empty.elim : Empty → V) ∘ (Empty.elim : Empty → Argument Empty)) =
      (Empty.elim : Empty → Argument V) := funext (fun i => i.elim)
  rw [free]
  change (eval E G ((argumentsIn ω n arg).mapNames Empty.elim) env ∧
    eval E G (translateFormula predicate (.variable ω) (fun i => .variable (arg i)) Empty.elim) env) ↔ _
  rw [argumentsIn_eval]
  constructor
  · rintro ⟨all,test⟩
    let reading : Fin n → D.Points := fun i => ⟨env (arg i),omega ▸ all i⟩
    exact ⟨reading,fun _ => rfl,(translateFormula_eval D predicate (.variable ω)
      (fun i => .variable (arg i)) Empty.elim env reading Empty.elim omega
      (fun _ => rfl) (fun i => i.elim)).mp test⟩
  · rintro ⟨points,same,holds⟩
    exact ⟨fun i => omega.symm ▸ same i ▸ (points i).property,
      (translateFormula_eval D predicate (.variable ω) (fun i => .variable (arg i))
        Empty.elim env points Empty.elim omega (fun i => (same i).symm) (fun i => i.elim)).mpr holds⟩

def arithmeticEnv {n : Nat} (omega : V) (args : Fin n → V) : Nat → V
  | 0 => omega
  | i+1 => if h : i < n then args ⟨i,h⟩ else omega

def arithmeticOn {n : Nat} (predicate : Semiformula ℒₒᵣ Empty n)
    (omega : V) (args : Fin n → V) : Prop :=
  eval E G ((arithmeticAt predicate 0 (fun i => i.val+1)).mapNames Empty.elim) (arithmeticEnv omega args)

theorem arithmeticOn_eval {L : ClassAxioms E G} {inh : Nonempty V} (D : OmegaDomain L inh)
    {n : Nat} (predicate : Semiformula ℒₒᵣ Empty n) (args : Fin n → V) :
    arithmeticOn (E := E) (G := G) predicate D.omega args ↔
      ∃ points : Fin n → D.Points, (∀ i, (points i).val = args i) ∧ predicate.Evalb points := by
  unfold arithmeticOn
  rw [arithmeticAt_eval D predicate (omega := rfl)]
  simp [arithmeticEnv]

theorem arithmeticOn_definable {n scope omega : Nat} {arg : Fin n → Nat}
    (predicate : Semiformula ℒₒᵣ Empty n) (ho : omega<scope) (ha : ∀ i, arg i<scope) :
    (ClassRelation.square E G).Definable scope
      (fun v => arithmeticOn (E := E) (G := G) predicate (v omega) (fun i => v (arg i))) := by
  let base := arithmeticAt predicate 0 (fun i => i.val+1)
  let indices : Nat → Nat := fun i => if h : i=0 then omega else
    if h : i-1<n then arg ⟨i-1,h⟩ else omega
  have inside (i : Nat) (_ : i<n+1) : indices i<scope := by
    unfold indices
    split
    · exact ho
    · split
      · apply ha
      · exact ho
  have commute (f : Formula Empty) (move : Nat → Nat) :
      (rename move f).mapNames (Empty.elim : Empty → V) = rename move (f.mapNames Empty.elim) := by
    induction f generalizing move <;> simp only [rename,Formula.mapNames,Argument.mapNames_rename, *]
  have mapped := commute base indices
  have scopeBase : Bound base (n+1) := arithmeticAt_scope predicate (by omega) (fun i => by have h:=i.isLt; omega)
  refine ⟨(rename indices base).toClassRelation,Formula.toClassRelation_scope _ (rename_bound _ scopeBase inside),?_⟩
  intro v
  rw [Formula.toClassRelation_eval,mapped,eval_rename]
  unfold arithmeticOn
  apply eval_congr
  · exact (mapNames_bound _ _ _).mpr scopeBase
  · intro i within
    cases i with
    | zero => simp [indices,arithmeticEnv]
    | succ i =>
      have hi : i<n := by omega
      simp [indices,arithmeticEnv,hi,Function.comp_apply]

end PalomarI3380.Logic.Expanded
