module
public import I3_380.ClassFormulaInterpretation
public import I3_380.UniformDensity
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext

open Logic Expanded
variable {V : Type} {E : V → V → Prop}
variable (h : ZFCModel E) (inh : Nonempty V)

local notation "K" => underlying h inh

def arguments (x y : V) : Nat → V
  | 0 => x
  | _+1 => y

theorem forced_binary_def (L : (K).OrderForcingLanguage) {p : Fragment V} (scope : p.bound 2)
    {n c x y : Nat} (hc : c < n) (hx : x < n) (hy : y < n) :
    (K).square.Definable n (fun env => (K).Forces p (env c) (arguments (env x) (env y))) := by
  let slot : Nat → Nat
    | 0 => c
    | 1 => x
    | _+2 => y
  have inside : ∀ k, k < 3 → slot k < n := by
    intro k _
    cases k with
    | zero => exact hc
    | succ k =>
      cases k with
      | zero => exact hx
      | succ k => exact hy
  have bound := Expanded.rename_bound (L.translation p) (L.translation_scope p scope) inside
  refine (base_definition h inh _ bound).congr fun env => ?_
  have envEq : env ∘ slot = pushValue (arguments (env x) (env y)) (env c) := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  exact (Expanded.eval_rename _ _ _ _ _).trans (by rw [envEq]; exact L.translation_eval p _ _)

theorem unary_parameter {P : (Nat → V) → Prop} (descr : (K).square.Definable 2 P) (value : V) :
    (K).GroundUnary (fun x => P (arguments x value)) := by
  obtain ⟨f,spec,meaning⟩ := formula_from_definition h inh descr
  let args : Nat → Argument V
    | 0 => .variable 0
    | _+1 => .named value
  have scope : ∀ i, i < 2 → (args i).bound 1 := by
    intro i _
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ _ => trivial
  refine ⟨f.substitute args,Expanded.substitute_bound f spec scope,fun env => ?_⟩
  have eq : (fun i => (args i).value env) = arguments (env 0) value := by
    funext i
    cases i <;> rfl
  exact (Expanded.eval_substitute _ _ _ _ _).trans (by rw [eq]; exact meaning _)

def Answered (p : Fragment V) (x q : V) : Prop :=
  (∃ y, (K).Forces p q (arguments x y)) ∨
    ¬∃ r y, (K).Refines r q ∧ (K).Forces p r (arguments x y)

theorem answered_def (L : (K).OrderForcingLanguage) {p : Fragment V} (scope : p.bound 2)
    {n c x : Nat} (hc : c < n) (hx : x < n) :
    (K).square.Definable n (fun s => Answered h inh p (s x) (s c)) := by
  have positive := forced_binary_def h inh L scope (n := n+1) (c := c+1) (x := x+1) (y := 0)
    (by omega) (by omega) (by omega)
  have extends_ := (K).refines_def (n := n+2) (p := 1) (q := c+2) (by omega) (by omega)
  have response := forced_binary_def h inh L scope (n := n+2) (c := 1) (x := x+2) (y := 0)
    (by omega) (by omega) (by omega)
  exact (Definable.ex positive).or (Definable.ex (Definable.ex (extends_.and response))).not

theorem answered_dense (p : Fragment V) (x : V) : (K).Dense (Answered h inh p x) := by
  classical
  intro q hq
  by_cases possible : ∃ r y, (K).Refines r q ∧ (K).Forces p r (arguments x y)
  · obtain ⟨r,y,below,witness⟩ := possible
    exact ⟨r,below,Or.inl ⟨y,witness⟩⟩
  · exact ⟨q,(K).refines_refl hq,Or.inr possible⟩

theorem answered_monotone (p : Fragment V) (x q r : V) (hqr : (K).Refines r q)
    (known : Answered h inh p x q) : Answered h inh p x r := by
  rcases known with ⟨y,witness⟩ | absent
  · exact Or.inl ⟨y,(K).force_refines p hqr _ witness⟩
  · exact Or.inr fun ⟨s,y,even,witness⟩ => absent ⟨s,y,(K).refines_trans even hqr,witness⟩

theorem answered_set (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {w : V} (omega : Internal.Omega E w) (regular : (K).Regular)
    {p : Fragment V} (scope : p.bound 2) (source : V) :
    ∃ q, G.filter q ∧ ∀ x, E x source → Answered h inh p x q := by
  let R : V → V → V → Prop := fun _ x q => Answered h inh p x q
  have definable : Definable.Relation3 K R := fun _ hx hq => answered_def h inh L scope hq hx
  have desc := Definable.boundedAll (S := (K).square) (n := 2) (i := 1) (by decide) _
    (answered_def h inh L scope (n := 3) (c := 1) (x := 0) (by decide) (by decide))
  have predicate := unary_parameter h inh desc source
  refine G.meets _ predicate (fun start valid => ?_)
  exact (K).meet_family omega regular (R := R) (key := start) definable valid
    (fun x _ => answered_dense h inh p x) (answered_monotone h inh p)

theorem answered_iff_witness (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {p : Fragment V} (scope : p.bound 2) {x q : V} (inside : G.filter q) (decision : Answered h inh p x q) :
    (∃ y, p.eval E G.order (arguments x y)) ↔ ∃ y, (K).Forces p q (arguments x y) := by
  constructor
  · rintro ⟨y,truth⟩
    rcases decision with found | absent
    · exact found
    · obtain ⟨s,sIn,actual⟩ := (G.forcing_truth L p scope (arguments x y)).mp truth
      obtain ⟨r,_,toQ,toS⟩ := G.directed q s inside sIn
      exact (absent ⟨r,y,toQ,(K).force_refines p toS _ actual⟩).elim
  · rintro ⟨y,witness⟩
    exact ⟨y,(G.forcing_truth L p scope (arguments x y)).mpr ⟨q,inside,witness⟩⟩

theorem generic_separation (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {w : V} (omega : Internal.Omega E w) (regular : (K).Regular)
    {R : V → V → Prop} (defn : Binary E G.order R) (source anchor : V) :
    ∃ output, ∀ x, E x output ↔ E x source ∧ R x anchor := by
  obtain ⟨formula,bound,meaning⟩ := defn
  let arg : Nat → Argument V
    | 0 => .variable 0
    | _+1 => .named anchor
  let body := formula.substitute arg
  have bodyScope : Expanded.Bound body 2 := Expanded.substitute_bound formula bound fun i _ => by
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ _ => trivial
  let p := body.fragment
  have scope : p.bound 2 := Expanded.fragment_scope body bodyScope
  have actual (x y : V) : p.eval E G.order (arguments x y) ↔ R x anchor := by
    exact (Expanded.fragment_eval E G.order body _).trans
      ((Expanded.eval_substitute E G.order formula arg _).trans (meaning _))
  obtain ⟨q,qIn,decision⟩ := answered_set h inh L G omega regular scope source
  have predicate := Definable.ex (forced_binary_def h inh L scope (n := 3) (c := 2) (x := 1) (y := 0)
    (by decide) (by decide) (by decide))
  obtain ⟨output,matched⟩ := (K).separate [] predicate source q
  refine ⟨output,fun x => (matched x).trans (and_congr_right fun hx => ?_)⟩
  refine (answered_iff_witness h inh L G scope qIn (decision x hx)).symm.trans ?_
  exact ⟨fun ⟨y,truth⟩ => (actual x y).mp truth,fun truth => ⟨anchor,(actual x anchor).mpr truth⟩⟩

theorem generic_replacement (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {w : V} (omega : Internal.Omega E w) (regular : (K).Regular)
    {R : V → V → Prop} (defn : Binary E G.order R)
    (functional : ∀ x y z, R x y → R x z → y = z) (source : V) :
    ∃ output, ∀ y, E y output ↔ ∃ x, E x source ∧ R x y := by
  obtain ⟨formula,bound,meaning⟩ := defn
  let p := formula.fragment
  have scope : p.bound 2 := Expanded.fragment_scope _ bound
  have interpret (x y : V) : p.eval E G.order (arguments x y) ↔ R x y :=
    (Expanded.fragment_eval _ _ _ _).trans (meaning _)
  obtain ⟨q,qIn,decision⟩ := answered_set h inh L G omega regular scope source
  have relation : Definable.Relation3 K (fun condition x y => (K).Forces p condition (arguments x y)) :=
    fun hc hx hy => forced_binary_def h inh L scope hc hx hy
  obtain ⟨_,cover,_,boundWitness⟩ := (K).collect_in_rank omega regular (R := fun condition x y => (K).Forces p condition (arguments x y)) relation q source
  have contains (x y : V) (hx : E x source) (holds : R x y) : E y cover := by
    have decided := (answered_iff_witness h inh L G scope qIn (decision x hx)).mp ⟨y,(interpret x y).mpr holds⟩
    obtain ⟨z,member,witness⟩ := boundWitness x hx decided
    have original := (interpret x z).mp ((G.forcing_truth L p scope (arguments x z)).mpr ⟨q,qIn,witness⟩)
    exact functional x z y original holds ▸ member
  let imageFormula := Expanded.Formula.ex (.and (.mem (.variable 0) (.named source)) formula)
  have imageScope : Expanded.Bound imageFormula 2 := by
    refine ⟨⟨(Nat.zero_lt_succ 2), trivial⟩, ?_⟩
    apply Expanded.bound_extension bound
    decide
  have image : Binary E G.order (fun y _ => ∃ x, E x source ∧ R x y) :=
    ⟨imageFormula,imageScope,fun s => exists_congr fun x => and_congr Iff.rfl (meaning (pushValue s x))⟩
  obtain ⟨output,contents⟩ := generic_separation h inh L G omega regular image cover cover
  refine ⟨output,fun y => (contents y).trans ⟨And.right,?_⟩⟩
  exact fun ⟨x,hx,hr⟩ => ⟨contains x y hx hr,x,hx,hr⟩

theorem generic_class_axioms (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {w : V} (omega : Internal.Omega E w) (regular : (K).Regular) : ClassAxioms E G.order :=
  ⟨h,fun _ => generic_separation h inh L G omega regular,
    fun _ => generic_replacement h inh L G omega regular⟩

end PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext
