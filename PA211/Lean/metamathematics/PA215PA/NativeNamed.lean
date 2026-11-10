import PA215PA.NativeCalculus
import PA215PA.Theory

/-! Literal named-formula syntax from NumericSyntax238.v at the same pinned
upstream. Its interpretation below is parameterized by two arithmetic binary
predicates R/E: it proves a logical translation schema, NOT the missing concrete
PA→S0→pointed calibration. Code1 encodes self-membership, not logical falsity. -/
namespace PA215.PA.NativeCalculus
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

inductive Named where
  | truth
  | imp (antecedent consequent : Named)
  | neg (body : Named)
  | mem (container member : Nat)
  | eq (left right : Nat)
  | all (name : Nat) (body : Named)
  deriving DecidableEq

def Named.encode : Named → Nat
  | .truth => 0
  | .imp p q => wim p.encode q.encode
  | .neg p => wn p.encode
  | .mem a b => wel a b
  | .eq a b => weq a b
  | .all a p => wal a p.encode

def bindEnv {n : Nat} (env : Nat → ArithmeticSemiterm Empty n) (a : Nat) :
    Nat → ArithmeticSemiterm Empty (n+1) :=
  fun v => if v = a then #0 else Rew.bShift (env v)

def Named.interpret (R E : ArithmeticSemisentence 2) :
    Named → {n : Nat} → (Nat → ArithmeticSemiterm Empty n) → ArithmeticSemisentence n
  | .truth, _, _ => ⊥ 🡒 ⊥
  | .imp p q, _, env => p.interpret R E env 🡒 q.interpret R E env
  | .neg p, _, env => ∼ p.interpret R E env
  | .mem a b, _, env => R/[env a,env b]
  | .eq a b, _, env => E/[env a,env b]
  | .all a p, _, env => ∀¹ p.interpret R E (bindEnv env a)

/-- Named semantics: quantifiers update exactly their bound label. -/
def Named.eval {V : Type*} (R E : V → V → Prop) : Named → (Nat → V) → Prop
  | .truth, _ => True
  | .imp p q, env => p.eval R E env → q.eval R E env
  | .neg p, env => ¬ p.eval R E env
  | .mem a b, env => R (env a) (env b)
  | .eq a b, env => E (env a) (env b)
  | .all a p, env => ∀ x, p.eval R E (fun v => if v = a then x else env v)

/-- Capture-correctness of the named-binder translation. No interpretation of
R/E as the concrete native set predicates is assumed. -/
theorem Named.interpret_correct {V : Type*} [ORingStructure V]
    (R E : ArithmeticSemisentence 2) (p : Named) {n : Nat}
    (env : Nat → ArithmeticSemiterm Empty n) (b : Fin n → V) :
    (V ⊧/b (p.interpret R E env)) ↔
      p.eval (fun x y => V ⊧/![x,y] R) (fun x y => V ⊧/![x,y] E)
        (fun v => Semiterm.val b Empty.elim (env v)) := by
  induction p generalizing n with
  | truth => simp [interpret,eval]
  | imp p q ihp ihq => simp [interpret,eval,ihp,ihq]
  | neg p ih => simp [interpret,eval,ih]
  | mem a c => simp [interpret,eval]
  | eq a c => simp [interpret,eval]
  | all a p ih =>
    simp only [interpret,Semiformula.eval_all,eval]
    apply forall_congr'
    intro x
    rw [ih]
    apply iff_of_eq
    congr 1
    funext v
    by_cases hv : v = a <;> simp [bindEnv,hv]

def namedRho2 (a : Nat) (p q : Named) : Named :=
  .imp (.all a (.imp p q)) (.imp (.all a p) (.all a q))

theorem namedRho2_encode (a : Nat) (p q : Named) :
    (namedRho2 a p q).encode = rho2 a p.encode q.encode := rfl

/-- An actual object-PA proof of the named rho2 translation schema for any
chosen arithmetic interpretations R/E of the two native atomic relations.
No concrete PA/native calibration is hidden in these parameters. -/
theorem pa_proves_namedRho2 (R E : ArithmeticSemisentence 2)
    (env : Nat → ArithmeticSemiterm Empty 0) (a : Nat) (p q : Named) :
    theory ⊢ (namedRho2 a p q).interpret R E env := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [namedRho2,Named.interpret,models_iff]
  intro hpq hp v
  exact hpq v (hp v)

#print axioms Named.interpret_correct
#print axioms namedRho2_encode
#print axioms pa_proves_namedRho2
end PA215.PA.NativeCalculus
