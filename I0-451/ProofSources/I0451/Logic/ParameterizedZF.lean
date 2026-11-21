module
public import I0451.Logic.SetLanguageCodes
public import Foundation.FirstOrder.SetTheory.ZF.ZF

/-! ZF schemata with explicitly bound finite parameter vectors.
This presentation has the same models as Foundation's ZF, whose
schemata instead use universal closure of open formulas. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def membershipAtom {n : Nat} (i j : Fin n) : SetTheorySemisentence n :=
  .rel Language.Set.Rel.mem ![#i,#j]

def equalityAtom {n : Nat} (i j : Fin n) : SetTheorySemisentence n :=
  .rel Language.Set.Rel.eq ![#i,#j]

def separationArgs {n : Nat} : Fin (n + 1) → ClosedSemiterm ℒₛₑₜ (n + 3) :=
  Fin.cases #0 fun j => #(j.addNat 3)

def replacementArgs {ξ : Type} {n d : Nat} (x y : Fin (n + d)) :
    Fin (n + 2) → Semiterm ℒₛₑₜ ξ (n + d) :=
  Fin.cases #x (Fin.cases #y fun j => #(j.addNat d))

def separationWithParameters {n : Nat} (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence n :=
  ∀¹ ∃¹ ∀¹ (membershipAtom 0 1 🡘 (membershipAtom 0 2 ⋏ (φ ⇜ separationArgs)))

def replacementWithParameters {n : Nat} (φ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence n :=
  (∀¹ ∃¹ ((φ ⇜ replacementArgs (d := 2) 1 0) ⋏
    (∀¹ ((φ ⇜ replacementArgs (d := 3) 2 0) 🡒 equalityAtom 0 1)))) 🡒
    (∀¹ ∃¹ ∀¹ (membershipAtom 0 1 🡘
      (∃¹ (membershipAtom 0 3 ⋏ (φ ⇜ replacementArgs (d := 4) 0 1)))))

def parameterizedSeparation : SetTheory :=
  { σ | ∃ (n : Nat) (φ : SetTheorySemisentence (n + 1)), σ = ∀¹* separationWithParameters φ }

def parameterizedReplacement : SetTheory :=
  { σ | ∃ (n : Nat) (φ : SetTheorySemisentence (n + 2)), σ = ∀¹* replacementWithParameters φ }

def parameterizedZF : SetTheory :=
  𝗕𝗦𝗧 ∪ parameterizedSeparation ∪ parameterizedReplacement

variable {V : Type} [SetStructure V] [Nonempty V]

set_option maxHeartbeats 500000 in
theorem separationWithParameters_eval {n : Nat} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    (separationWithParameters φ).Evalb v ↔
      ∀ x : V, ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ φ.Evalb (z :> v) := by
  have arguments (x y z : V) :
      (Semiterm.val (z :> y :> x :> v) Empty.elim ∘ separationArgs) = z :> v := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      have same : i.addNat 3 = i.succ.succ.succ := Fin.ext (by simp)
      simp [separationArgs, same]
  simp [separationWithParameters, membershipAtom, Semiformula.Evalb.eq_1,
    Semiformula.eval_substs, arguments] <;> rfl

set_option maxHeartbeats 500000 in
theorem replacementWithParameters_eval {n : Nat} (φ : SetTheorySemisentence (n + 2)) (v : Fin n → V) :
    (replacementWithParameters φ).Evalb v ↔
      (∀ x : V, ∃! y : V, φ.Evalb (x :> y :> v)) →
        ∀ A : V, ∃ B : V, ∀ y : V, y ∈ B ↔ ∃ x ∈ A, φ.Evalb (x :> y :> v) := by
  have args {d : Nat} (b : Fin (n + d) → V) (x y : Fin (n + d))
      (tail : ∀ i : Fin n, b (i.addNat d) = v i) :
      (Semiterm.val b Empty.elim ∘ replacementArgs x y) = b x :> b y :> v := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simp [replacementArgs, tail]
  have p2 (a b : V) (i : Fin n) : (a :> b :> v) (i.addNat 2) = v i := by
    rw [show i.addNat 2 = i.succ.succ from Fin.ext (by simp)]
    rfl
  have p3 (a b c : V) (i : Fin n) : (a :> b :> c :> v) (i.addNat 3) = v i := by
    rw [show i.addNat 3 = i.succ.succ.succ from Fin.ext (by simp)]
    rfl
  have p4 (a b c d : V) (i : Fin n) : (a :> b :> c :> d :> v) (i.addNat 4) = v i := by
    rw [show i.addNat 4 = i.succ.succ.succ.succ from Fin.ext (by simp)]
    rfl
  simp [replacementWithParameters, membershipAtom, equalityAtom, Semiformula.Evalb.eq_1,
    Semiformula.eval_substs, args _ _ _ (p2 _ _), args _ _ _ (p3 _ _ _), args _ _ _ (p4 _ _ _ _),
    ExistsUnique] <;> rfl

private theorem separation_definable {n : Nat} (φ : SetTheorySemisentence (n + 1))
    (parameters : Fin n → V) : ℒₛₑₜ-predicate (fun x : V => φ.Evalb (x :> parameters)) := by
  let args : Fin (n + 1) → SetTheorySemiterm V 1 := #0 :> fun i => &(parameters i)
  refine ⟨(Rew.embSubsts args) ▹ φ, fun v => ?_⟩
  rw [Semiformula.eval_embSubsts]
  have same : (Semiterm.val (L := ℒₛₑₜ) v id ∘ args) = (v 0 :> parameters) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [same]

private theorem replacement_definable {n : Nat} (φ : SetTheorySemisentence (n + 2))
    (parameters : Fin n → V) : ℒₛₑₜ-relation (fun x y : V => φ.Evalb (x :> y :> parameters)) := by
  let args : Fin (n + 2) → SetTheorySemiterm V 2 := #0 :> #1 :> fun i => &(parameters i)
  refine ⟨(Rew.embSubsts args) ▹ φ, fun v => ?_⟩
  rw [Semiformula.eval_embSubsts]
  have same : (Semiterm.val (L := ℒₛₑₜ) v id ∘ args) = (v 0 :> v 1 :> parameters) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  rw [same]

theorem parameterizedZF_of_zf [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    V↓[ℒₛₑₜ] ⊧* parameterizedZF := by
  constructor
  rintro p ((basic | ⟨n, φ, rfl⟩) | ⟨n, φ, rfl⟩)
  · exact Theory.models V 𝗕𝗦𝗧 basic
  · simp only [models_iff, Semiformula.eval_allClosure, ← Semiformula.Evalb.eq_1]
    intro env
    exact (separationWithParameters_eval φ env).mpr fun x => separation_exists x _ (separation_definable φ env)
  · simp only [models_iff, Semiformula.eval_allClosure, ← Semiformula.Evalb.eq_1]
    intro env
    exact (replacementWithParameters_eval φ env).mpr fun total X =>
      replacement_rel_exists X _ total (replacement_definable φ env)

private def combineParameters {n k : Nat} (head : Fin n → V) (tail : Fin k → V) : Fin (k + n) → V :=
  Fin.append head tail ∘ Fin.cast (Nat.add_comm k n)

private theorem combineParameters_cons {n k : Nat} (x : V) (head : Fin n → V) (tail : Fin k → V) :
    combineParameters (x :> head) tail = x :> combineParameters head tail := by
  change Fin.append (Fin.cons x head) tail ∘ _ = Fin.cons x (combineParameters head tail)
  rw [Fin.append_cons]
  unfold combineParameters
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem parameterAssignment {n : Nat} (a : Fin n) (φ : SetTheorySemiproposition n) :
    ∃ (k : Nat) (body : SetTheorySemisentence (k + n)),
      ∀ v : Nat → V, ∃ tail : Fin k → V, ∀ u : Fin n → V,
        body.Evalb (combineParameters u tail) ↔ φ.Eval u v := by
  classical
  let k := φ.fvSup
  let lift (i : Fin n) : Fin (k + n) := Fin.cast (Nat.add_comm n k) (Fin.castAdd k i)
  let params (i : Fin k) : Fin (k + n) := Fin.cast (Nat.add_comm n k) (Fin.natAdd n i)
  let f (x : Nat) : Fin (k + n) := if h : x < k then params ⟨x,h⟩ else lift a
  let relabel : Rew ℒₛₑₜ Nat n Empty (k + n) := Rew.bind (fun i => #(lift i)) (fun x => #(f x))
  refine ⟨k, relabel ▹ φ, fun v => ⟨fun j => v j.val, fun u => ?_⟩⟩
  rw [Semiformula.Evalb.eq_1, Semiformula.eval_rew]
  have value (i : Fin n) : combineParameters u (fun j => v j.val) (lift i) = u i := by
    simp [combineParameters, lift]
  have values : (fun i : Fin n =>
      Semiterm.val (combineParameters u (fun j => v j.val)) Empty.elim (relabel #i)) = u := by
    funext i
    exact value i
  simp only [Function.comp_def] at *
  rw [values]
  apply Semiformula.eval_iff_of_funEqOn φ
  intro x appears
  have h : x < k := Semiformula.lt_fvSup_of_fvar? appears
  simp [relabel, f, h, params, combineParameters]
  rw [show (⟨x + n, by omega⟩ : Fin (n + k)) = Fin.natAdd n ⟨x,h⟩ from
    Fin.ext (by simp [Nat.add_comm])]
  exact Fin.append_right u (fun j : Fin k => v j.val) ⟨x,h⟩

private theorem combineParameters_empty {k : Nat} (tail : Fin k → V) (head : Fin 0 → V) :
    combineParameters head tail = tail := by
  unfold combineParameters
  rw [Fin.append_left_nil _ _ rfl]
  rfl

theorem zf_of_parameterizedZF [M : V↓[ℒₛₑₜ] ⊧* parameterizedZF] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  rintro p ((basic | sep) | repl)
  · exact M.models_set (.inl (.inl basic))
  · cases sep with
    | separation φ =>
      simp only [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
      simp [Matrix.comp_vecCons', Function.comp_def]
      intro f x
      obtain ⟨k, body, witness⟩ := parameterAssignment (V := V) 0 φ
      obtain ⟨env, agrees⟩ := witness f
      have axiomModel : V↓[ℒₛₑₜ] ⊧ (∀¹* separationWithParameters body : SetTheorySentence) :=
        M.models_set (.inl (.inr ⟨k,body,rfl⟩))
      have core := (Semiformula.eval_allClosure.mp (models_iff.mp axiomModel)) env
      obtain ⟨Y, hy⟩ := (separationWithParameters_eval body env).mp core x
      refine ⟨Y, fun z => ?_⟩
      have instanceOf := agrees ![z]
      rw [combineParameters_cons, combineParameters_empty] at instanceOf
      exact (hy z).trans (and_congr_right fun _ => by simpa [Matrix.vec_single_eq_const] using instanceOf)
  · cases repl with
    | replacement φ =>
      simp only [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
      intro f
      obtain ⟨k, body, witness⟩ := parameterAssignment (V := V) 0 φ
      obtain ⟨env, agrees⟩ := witness f
      have axiomModel : V↓[ℒₛₑₜ] ⊧ (∀¹* replacementWithParameters body : SetTheorySentence) :=
        M.models_set (.inr ⟨k,body,rfl⟩)
      have core := (Semiformula.eval_allClosure.mp (models_iff.mp axiomModel)) env
      have truth (x y : V) : body.Evalb (x :> y :> env) ↔ φ.Eval ![x,y] f := by
        have inst := agrees ![x,y]
        rw [combineParameters_cons, combineParameters_cons, combineParameters_empty] at inst
        exact inst
      simpa [truth, Matrix.comp_vecCons', Function.comp_def, Matrix.vec_single_eq_const] using
        (replacementWithParameters_eval body env).mp core

end I0451.Logic
