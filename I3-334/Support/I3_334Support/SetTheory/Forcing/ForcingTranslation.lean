module
public import I3_334Support.SetTheory.Forcing.ClassForcing
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
open Logic.Expanded (Argument Fragment)
variable {A V : Type} {M : Algebra A} {N : SetContext M V}

namespace OrderForcingLanguage

variable (L : N.OrderForcingLanguage)

def edgeArgs (p x y : Argument V) : Nat → Argument V
  | 0 => p
  | 1 => x
  | _ + 2 => y

def strengthen (q p : Argument V) : Expanded.Formula V :=
  L.refines.substitute (Expanded.ClassRelation.formulaArguments q p)

def orderTest (p x y : Argument V) : Expanded.Formula V :=
  L.edge.substitute (edgeArgs p x y)

def coverTest (p x : Argument V) : Expanded.Formula V :=
  L.covers.substitute (Expanded.ClassRelation.formulaArguments p x)

theorem strengthen_scope {d : Nat} {q p : Argument V} (hq : q.bound d) (hp : p.bound d) :
    Expanded.Bound (L.strengthen q p) d :=
  Expanded.substitute_bound _ L.refines_scope fun i _ => by
    simp only [Expanded.ClassRelation.formulaArguments]
    split <;> assumption

theorem orderTest_scope {d : Nat} {p x y : Argument V} (hp : p.bound d) (hx : x.bound d) (hy : y.bound d) :
    Expanded.Bound (L.orderTest p x y) d :=
  Expanded.substitute_bound _ L.edge_scope fun i _ => by
    cases i with
    | zero => exact hp
    | succ i =>
      cases i with
      | zero => exact hx
      | succ i => exact hy

theorem coverTest_scope {d : Nat} {p x : Argument V} (hp : p.bound d) (hx : x.bound d) :
    Expanded.Bound (L.coverTest p x) d :=
  Expanded.substitute_bound _ L.covers_scope fun i _ => by
    simp only [Expanded.ClassRelation.formulaArguments]
    split <;> assumption

abbrev ground : Expanded.Formula V → (Nat → V) → Prop :=
  Expanded.eval N.mem (fun _ _ => False)

theorem strengthen_eval (q p : Argument V) (s : Nat → V) :
    ground (N := N) (L.strengthen q p) s ↔ N.Refines (q.value s) (p.value s) :=
  (Expanded.eval_substitute _ _ _ _ _).trans (L.refines_eval _)

theorem orderTest_eval (p x y : Argument V) (s : Nat → V) :
    ground (N := N) (L.orderTest p x y) s ↔ N.OrderEdge (p.value s) (x.value s) (y.value s) :=
  (Expanded.eval_substitute _ _ _ _ _).trans (L.edge_eval _)

theorem coverTest_eval (p x : Argument V) (s : Nat → V) :
    ground (N := N) (L.coverTest p x) s ↔ N.Covers (p.value s) (x.value s) :=
  (Expanded.eval_substitute _ _ _ _ _).trans (L.covers_eval _)

def negSlots : Nat → Nat
  | 0 => 0
  | n + 1 => n + 2

def exSlots : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 4

/-- The leading free variable names the condition. Negation and the
existential clause quantify over stronger conditions in the base model. -/
def translation : Fragment V → Expanded.Formula V
  | .bot => .bot
  | .eq a b => .eq (a.rename Nat.succ) (b.rename Nat.succ)
  | .mem a b => .mem (a.rename Nat.succ) (b.rename Nat.succ)
  | .order a b => L.orderTest (.variable 0) (a.rename Nat.succ) (b.rename Nat.succ)
  | .and a b => .and (translation a) (translation b)
  | .neg a => .all (.imp (L.strengthen (.variable 0) (.variable 1))
      (Expanded.neg (Expanded.rename negSlots (translation a))))
  | .ex a => .all (.imp (L.strengthen (.variable 0) (.variable 1))
      (.ex (.and (L.strengthen (.variable 0) (.variable 1)) (.ex (Expanded.rename exSlots (translation a))))))

private theorem negSlots_bound {i n : Nat} (h : i < n + 1) : negSlots i < n + 2 := by
  cases i with
  | zero => simp [negSlots]
  | succ k => change k + 2 < n + 2; omega

private theorem exSlots_bound {i n : Nat} (h : i < n + 2) : exSlots i < n + 4 := by
  cases i with
  | zero => simp [exSlots]
  | succ k =>
    cases k with
    | zero => simp [exSlots]
    | succ k => change k + 4 < n + 4; omega

theorem translation_scope (p : Fragment V) {n : Nat} (h : p.bound n) :
    Expanded.Bound (L.translation p) (n + 1) := by
  induction p generalizing n with
  | bot => trivial
  | eq a b | mem a b =>
    exact ⟨Expanded.arg_rename_bound h.1 (fun _ => Nat.succ_lt_succ),
      Expanded.arg_rename_bound h.2 (fun _ => Nat.succ_lt_succ)⟩
  | order a b =>
    exact L.orderTest_scope (Nat.zero_lt_succ _)
      (Expanded.arg_rename_bound h.1 (fun _ => Nat.succ_lt_succ))
      (Expanded.arg_rename_bound h.2 (fun _ => Nat.succ_lt_succ))
  | and a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | neg a ih =>
    exact ⟨L.strengthen_scope (q := .variable 0) (p := .variable 1) (Nat.zero_lt_succ _) (by change 1 < _; omega), ⟨Expanded.rename_bound _ (ih h)
      (fun _ => negSlots_bound), trivial⟩⟩
  | ex a ih =>
    exact ⟨L.strengthen_scope (q := .variable 0) (p := .variable 1) (Nat.zero_lt_succ _) (by change 1 < _; omega),
      ⟨L.strengthen_scope (q := .variable 0) (p := .variable 1) (Nat.zero_lt_succ _) (by change 1 < _; omega),
        Expanded.rename_bound _ (ih h) (fun _ => exSlots_bound)⟩⟩

private theorem negEnv (s : Nat → V) (p q : V) :
    pushValue (pushValue s p) q ∘ negSlots = pushValue s q := by
  funext i
  cases i <;> rfl

private theorem exEnv (s : Nat → V) (p q r x : V) :
    pushValue (pushValue (pushValue (pushValue s p) q) r) x ∘ exSlots = pushValue (pushValue s x) r := by
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem translation_eval (formula : Fragment V) (p : V) (env : Nat → V) :
    ground (N := N) (L.translation formula) (pushValue env p) ↔ N.Forces formula p env := by
  induction formula generalizing p env with
  | bot => rfl
  | eq a b | mem a b =>
    simp only [translation, ground, Expanded.eval, Expanded.eval_argument_rename, Forces]
    rfl
  | order a b =>
    rw [translation, L.orderTest_eval]
    simp only [Expanded.eval_argument_rename]
    rfl
  | and a b ia ib => exact and_congr (ia p env) (ib p env)
  | neg a ih =>
    change (∀ q, ground (N := N) (L.strengthen (.variable 0) (.variable 1)) (pushValue (pushValue env p) q) →
      ¬ground (N := N) (Expanded.rename negSlots (L.translation a)) (pushValue (pushValue env p) q)) ↔ _
    apply forall_congr'
    intro q
    refine imp_congr (L.strengthen_eval _ _ _) (not_congr ?_)
    exact (Expanded.eval_rename _ _ _ _ _).trans (by rw [negEnv]; exact ih q env)
  | ex a ih =>
    change (∀ q, ground (N := N) (L.strengthen (.variable 0) (.variable 1)) (pushValue (pushValue env p) q) →
      ∃ r, ground (N := N) (L.strengthen (.variable 0) (.variable 1)) (pushValue (pushValue (pushValue env p) q) r) ∧
      ∃ x, ground (N := N) (Expanded.rename exSlots (L.translation a))
        (pushValue (pushValue (pushValue (pushValue env p) q) r) x)) ↔ _
    apply forall_congr'
    intro q
    refine imp_congr (L.strengthen_eval _ _ _) ?_
    apply exists_congr
    intro r
    refine and_congr (L.strengthen_eval _ _ _) ?_
    apply exists_congr
    intro x
    exact (Expanded.eval_rename _ _ _ _ _).trans (by rw [exEnv]; exact ih r (pushValue env x))

end OrderForcingLanguage

namespace OrdinaryContext

variable {E : V → V → Prop} (h : ZFCModel E) (inhabited : Nonempty V)

noncomputable abbrev underlying :=
  (Expanded.ClassAxioms.from_ordinary h).context inhabited

theorem formula_from_definition {n : Nat} {predicate : (Nat → V) → Prop}
    (defn : (underlying h inhabited).square.Definable n predicate) :
    ∃ f : Expanded.Formula V, Expanded.Bound f n ∧
      ∀ env, Expanded.eval E (fun _ _ => False) f env ↔ predicate env := by
  obtain ⟨p, scope, meaning⟩ := defn
  exact ⟨Expanded.ClassRelation.compile p, Expanded.ClassRelation.compile_scope p scope,
    fun env => (Expanded.ClassRelation.compile_eval p env).trans (meaning env)⟩

theorem forcing_language_exists : Nonempty (OrderForcingLanguage (underlying h inhabited)) := by
  let N := underlying h inhabited
  obtain ⟨r, rScope, rEval⟩ := formula_from_definition h inhabited
    (N.refines_def (n := 2) (p := 0) (q := 1) (by decide) (by decide))
  obtain ⟨e, eScope, eEval⟩ := formula_from_definition h inhabited
    (N.orderEdge_def (n := 3) (p := 0) (x := 1) (y := 2) (by decide) (by decide) (by decide))
  obtain ⟨c, cScope, cEval⟩ := formula_from_definition h inhabited
    (N.covers_def (n := 2) (p := 0) (x := 1) (by decide) (by decide))
  exact ⟨r,rScope,rEval,e,eScope,eEval,c,cScope,cEval⟩

end OrdinaryContext
end PalomarI3380.SquareRepresentation.SetContext
