module
public import I3_334Support.Logic.Expanded
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type}

def Argument.substitute (f : Nat → Argument V) : Argument V → Argument V
  | .variable i => f i
  | .named p => .named p

def liftNames (f : Nat → Argument V) : Nat → Argument V
  | 0 => .variable 0
  | i + 1 => (f i).rename Nat.succ

def Formula.substitute (f : Nat → Argument V) : Formula V → Formula V
  | .bot => .bot
  | .eq x y => .eq (x.substitute f) (y.substitute f)
  | .mem x y => .mem (x.substitute f) (y.substitute f)
  | .order x y => .order (x.substitute f) (y.substitute f)
  | .and p q => .and (p.substitute f) (q.substitute f)
  | .or p q => .or (p.substitute f) (q.substitute f)
  | .imp p q => .imp (p.substitute f) (q.substitute f)
  | .all p => .all (p.substitute (liftNames f))
  | .ex p => .ex (p.substitute (liftNames f))

theorem Argument.substitute_bound (x : Argument V) {f : Nat → Argument V} {n m : Nat}
    (h : x.bound n) (where_ : ∀ i, i < n → (f i).bound m) :
    (x.substitute f).bound m := by
  cases x with
  | «variable» i => exact where_ i h
  | named => trivial

theorem substitute_bound (p : Formula V) {f : Nat → Argument V} {n m : Nat}
    (hp : Bound p n) (bounded : ∀i, i < n → (f i).bound m) :
    Bound (p.substitute f) m := by
  induction p generalizing f n m with
  | bot => trivial
  | eq x y | mem x y | order x y =>
    exact ⟨x.substitute_bound hp.1 bounded,y.substitute_bound hp.2 bounded⟩
  | and p q ip iq | or p q ip iq | imp p q ip iq => exact ⟨ip hp.1 bounded,iq hp.2 bounded⟩
  | all p ih | ex p ih =>
    apply ih hp
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact arg_rename_bound (bounded i (by omega)) (fun _ => Nat.succ_lt_succ)

theorem Argument.substitute_value (x : Argument V) (f : Nat → Argument V) (env : Nat → V) :
    (x.substitute f).value env = x.value (fun i => (f i).value env) := by
  cases x <;> rfl

theorem eval_substitute (E G : V → V → Prop) (p : Formula V) (f : Nat → Argument V) (env : Nat → V) :
    eval E G (p.substitute f) env ↔ eval E G p (fun i => (f i).value env) := by
  have extension (env : Nat → V) (z : V) (f : Nat → Argument V) :
      (fun i => (liftNames f i).value (pushValue env z)) =
        pushValue (fun i => (f i).value env) z := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact eval_argument_rename (f i) Nat.succ (pushValue env z)
  induction p generalizing f env <;> simp only [Formula.substitute, eval, Argument.substitute_value, *]

theorem Argument.eval_congr (x : Argument V) {n : Nat} (h : x.bound n) {s t : Nat → V}
    (same : ∀ i, i < n → s i = t i) : x.value s = x.value t := by
  cases x with
  | «variable» i => exact same i h
  | named => rfl

private theorem push_agreement {n : Nat} {s t : Nat → V}
    (h : ∀ i, i < n → s i = t i) (x : V) : ∀ i, i < n + 1 → pushValue s x i = pushValue t x i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact h i (by omega)

theorem eval_congr (E G : V → V → Prop) (p : Formula V) {n : Nat} (hp : Bound p n) {s t : Nat → V}
    (same : ∀ i, i < n → s i = t i) : eval E G p s ↔ eval E G p t := by
  induction p generalizing n s t with
  | bot => rfl
  | eq x y | mem x y | order x y =>
    simp only [eval, x.eval_congr hp.1 same, y.eval_congr hp.2 same]
  | and p q ip iq | or p q ip iq | imp p q ip iq =>
    simp only [eval, ip hp.1 same, iq hp.2 same]
  | all p ih =>
    change (∀ x, eval E G p (pushValue s x)) ↔ _
    exact forall_congr' fun x => ih hp (push_agreement same x)
  | ex p ih =>
    change (∃ x, eval E G p (pushValue s x)) ↔ _
    exact exists_congr fun x => ih hp (push_agreement same x)

end PalomarI3380.Logic.Expanded
