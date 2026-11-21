module
public import I3_380.Logic.Syntax
@[expose] public section

namespace PalomarI3380.Logic.Expanded

/-- Names are external parameters in an ordinary first-order definition.
Only the set variables take part in binder renaming. -/
inductive Argument (V : Type) where
  | «variable» (index : Nat)
  | named (value : V)

def Argument.bound : Argument V → Nat → Prop
  | .variable i, n => i < n
  | .named _, _ => True

def Argument.value : Argument V → (Nat → V) → V
  | .variable i, s => s i
  | .named x, _ => x

def Argument.rename (σ : Nat → Nat) : Argument V → Argument V
  | .variable i => .variable (σ i)
  | .named p => .named p

inductive Formula (V : Type) where
  | bot
  | eq (x y : Argument V)
  | mem (x y : Argument V)
  | order (x y : Argument V)
  | and (left right : Formula V)
  | or (left right : Formula V)
  | imp (left right : Formula V)
  | all (body : Formula V)
  | ex (body : Formula V)

def Bound : Formula V → Nat → Prop
  | .bot, _ => True
  | .eq x y, n | .mem x y, n | .order x y, n => x.bound n ∧ y.bound n
  | .and p q, n | .or p q, n | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n | .ex p, n => Bound p (n + 1)

def rename (σ : Nat → Nat) : Formula V → Formula V
  | .bot => .bot
  | .eq x y => .eq (x.rename σ) (y.rename σ)
  | .mem x y => .mem (x.rename σ) (y.rename σ)
  | .order x y => .order (x.rename σ) (y.rename σ)
  | .and p q => .and (rename σ p) (rename σ q)
  | .or p q => .or (rename σ p) (rename σ q)
  | .imp p q => .imp (rename σ p) (rename σ q)
  | .all p => .all (rename (Logic.lift σ) p)
  | .ex p => .ex (rename (Logic.lift σ) p)

def eval (E G : V → V → Prop) : Formula V → (Nat → V) → Prop
  | .bot, _ => False
  | .eq x y, s => x.value s = y.value s
  | .mem x y, s => E (x.value s) (y.value s)
  | .order x y, s => G (x.value s) (y.value s)
  | .and p q, s => eval E G p s ∧ eval E G q s
  | .or p q, s => eval E G p s ∨ eval E G q s
  | .imp p q, s => eval E G p s → eval E G q s
  | .all p, s => ∀ x, eval E G p (pushValue s x)
  | .ex p, s => ∃ x, eval E G p (pushValue s x)

def neg (p : Formula V) : Formula V := .imp p .bot

theorem arg_rename_bound {x : Argument V} {σ : Nat → Nat} {n m : Nat} (h : x.bound n)
    (under : ∀i, i < n → σ i < m) : (x.rename σ).bound m := by
  cases x with
  | named => trivial
  | «variable» i => exact under i h

theorem rename_bound (p : Formula V) {σ : Nat → Nat} {n m : Nat} (h : Bound p n)
    (under : ∀ i, i < n → σ i < m) : Bound (rename σ p) m := by
  induction p generalizing σ n m with
  | bot => trivial
  | eq x y | mem x y | order x y => exact ⟨arg_rename_bound h.1 under, arg_rename_bound h.2 under⟩
  | and p q ip iq | or p q ip iq | imp p q ip iq => exact ⟨ip h.1 under, iq h.2 under⟩
  | all p ih | ex p ih =>
    apply ih h
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact Nat.succ_lt_succ (under i (by omega))

theorem bound_extension {p : Formula V} {n m : Nat} (hp : Bound p n) (large : n ≤ m) : Bound p m := by
  induction p generalizing n m with
  | bot => trivial
  | eq a b | mem a b | order a b =>
    have monotone (x : Argument V) (h : x.bound n) : x.bound m := by
      cases x with
      | «variable» i => exact Nat.lt_of_lt_of_le h large
      | named => trivial
    exact ⟨monotone a hp.1,monotone b hp.2⟩
  | and a b ia ib | or a b ia ib | imp a b ia ib => exact ⟨ia hp.1 large,ib hp.2 large⟩
  | all a ih | ex a ih => exact ih hp (Nat.succ_le_succ large)

theorem eval_argument_rename (i : Argument V) (σ : Nat → Nat) (s : Nat → V) :
    (i.rename σ).value s = i.value (s ∘ σ) := by
  cases i <;> rfl

theorem eval_rename (E G : V → V → Prop) (p : Formula V) (σ : Nat → Nat) (env : Nat → V) :
    eval E G (rename σ p) env ↔ eval E G p (env ∘ σ) := by
  have under (env : Nat → V) (x : V) (σ : Nat → Nat) :
      pushValue env x ∘ Logic.lift σ = pushValue (env ∘ σ) x := by
    funext n
    cases n <;> rfl
  induction p generalizing env σ <;> simp only [rename, eval, eval_argument_rename, *]

/-- First-order binary classes of an expanded membership structure. -/
def Binary (E G : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∃ p : Formula V, Bound p 2 ∧ ∀ env, eval E G p env ↔ r (env 0) (env 1)

namespace Binary

variable {E G : V → V → Prop} {r s : V → V → Prop}

theorem congr (h : Binary E G r) (eq : ∀ x y, r x y ↔ s x y) : Binary E G s := by
  obtain ⟨p,scope,meaning⟩ := h
  exact ⟨p,scope,fun env => (meaning env).trans (eq _ _)⟩

theorem equality : Binary E G Eq :=
  ⟨.eq (.variable 0) (.variable 1), by simp [Bound, Argument.bound], fun _ => Iff.rfl⟩

theorem membership : Binary E G E :=
  ⟨.mem (.variable 0) (.variable 1), by simp [Bound, Argument.bound], fun _ => Iff.rfl⟩

theorem globalOrder : Binary E G G :=
  ⟨.order (.variable 0) (.variable 1), by simp [Bound, Argument.bound], fun _ => Iff.rfl⟩

theorem universal : Binary E G (fun _ _ => True) :=
  ⟨neg .bot, ⟨trivial,trivial⟩,fun _ => ⟨fun _ => trivial, fun _ h => h⟩⟩

theorem complement (h : Binary E G r) : Binary E G (fun x y => ¬r x y) := by
  obtain ⟨p,scope,meaning⟩ := h
  exact ⟨neg p, ⟨scope,trivial⟩, fun env => not_congr (meaning env)⟩

theorem intersection (h₁ : Binary E G r) (h₂ : Binary E G s) : Binary E G (fun x y => r x y ∧ s x y) := by
  obtain ⟨p,bp,hp⟩ := h₁
  obtain ⟨q,bq,hq⟩ := h₂
  exact ⟨.and p q, ⟨bp,bq⟩, fun env => and_congr (hp env) (hq env)⟩

theorem converse (h : Binary E G r) : Binary E G (fun x y => r y x) := by
  obtain ⟨p,scope,meaning⟩ := h
  let swap (i : Nat) := if i = 0 then 1 else 0
  have bound : ∀ i, i < 2 → swap i < 2 := by intro i _; unfold swap; split <;> omega
  exact ⟨rename swap p, rename_bound p scope bound, fun env =>
    (eval_rename E G p swap env).trans (meaning (env ∘ swap))⟩

theorem product (hp : Binary E G r) (hq : Binary E G s) :
    Binary E G (fun x y => ∃ z, r x z ∧ s z y) := by
  obtain ⟨p,bp,rp⟩ := hp
  obtain ⟨q,bq,rq⟩ := hq
  let left (i : Nat) := if i = 0 then 1 else 0
  let right (i : Nat) := if i = 0 then 0 else 2
  have boundL : ∀ i, i < 2 → left i < 3 := by intro i _; unfold left; split <;> omega
  have boundR : ∀ i, i < 2 → right i < 3 := by intro i _; unfold right; split <;> omega
  refine ⟨.ex (.and (rename left p) (rename right q)),
    ⟨rename_bound p bp boundL, rename_bound q bq boundR⟩,fun env => ?_⟩
  apply exists_congr
  intro x
  exact and_congr ((eval_rename E G p left _).trans (rp _)) ((eval_rename E G q right _).trans (rq _))

theorem column (x : V) : Binary E G (fun y z => y = x ∧ z = x) :=
  ⟨.and (.eq (.variable 0) (.named x)) (.eq (.variable 1) (.named x)),
    by simp [Bound, Argument.bound],fun _ => Iff.rfl⟩

end Binary
end PalomarI3380.Logic.Expanded
