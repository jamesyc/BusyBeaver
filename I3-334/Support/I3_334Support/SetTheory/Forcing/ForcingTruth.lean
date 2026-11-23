module
public import I3_334Support.SetTheory.Forcing.GenericOrder
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic Expanded
variable {A V : Type} {M : Algebra A} {N : SetContext M V}

theorem GroundUnary.or {p q : V → Prop} (first : N.GroundUnary p) (second : N.GroundUnary q) :
    N.GroundUnary (fun r => p r ∨ q r) := by
  obtain ⟨f, hf, describes⟩ := first
  obtain ⟨g, hg, also⟩ := second
  exact ⟨.or f g, ⟨hf,hg⟩, fun s => or_congr (describes s) (also s)⟩

theorem GroundUnary.and {p q : V → Prop} (first : N.GroundUnary p) (second : N.GroundUnary q) :
    N.GroundUnary (fun r => p r ∧ q r) := by
  obtain ⟨f, hf, describes⟩ := first
  obtain ⟨g, hg, also⟩ := second
  exact ⟨.and f g, ⟨hf,hg⟩, fun s => and_congr (describes s) (also s)⟩

theorem GroundUnary.not {p : V → Prop} (first : N.GroundUnary p) : N.GroundUnary (fun r => ¬p r) := by
  obtain ⟨f, hf, describes⟩ := first
  exact ⟨Expanded.neg f,⟨hf,trivial⟩,fun s => not_congr (describes s)⟩

def Compatible (N : SetContext M V) (p q : V) : Prop :=
  ∃ r, N.Refines r p ∧ N.Refines r q

namespace OrderForcingLanguage

variable (L : N.OrderForcingLanguage)
include L

theorem force_unary (p : Fragment V) {n : Nat} (bounded : p.bound n) (values : Nat → V) :
    N.GroundUnary (fun q => N.Forces p q values) := by
  let arguments : Nat → Argument V
    | 0 => .variable 0
    | i+1 => .named (values i)
  have scope (i : Nat) : (arguments i).bound 1 := by
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => trivial
  refine ⟨(L.translation p).substitute arguments, Expanded.substitute_bound _ (L.translation_scope p bounded)
    (fun i _ => scope i), fun env => ?_⟩
  refine (Expanded.eval_substitute N.mem _ _ _ env).trans ?_
  have same : (fun i => (arguments i).value env) = pushValue values (env 0) := by
    funext i
    cases i <;> rfl
  rw [same]
  exact L.translation_eval p _ _

theorem force_witness (p : Fragment V) {n : Nat} (bounded : p.bound (n+1)) (values : Nat → V) :
    N.GroundUnary (fun q => ∃ x, N.Forces p q (pushValue values x)) := by
  let arguments : Nat → Argument V
    | 0 => .variable 1
    | 1 => .variable 0
    | i+2 => .named (values i)
  have scope (i : Nat) : (arguments i).bound 2 := by
    cases i with
    | zero => exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
    | succ i =>
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ _ => trivial
  refine ⟨.ex ((L.translation p).substitute arguments), Expanded.substitute_bound _ (L.translation_scope p bounded)
    (fun i _ => scope i), fun env => ?_⟩
  apply exists_congr
  intro x
  refine (Expanded.eval_substitute _ _ _ _ _).trans ?_
  have same : (fun i => (arguments i).value (pushValue env x)) =
      pushValue (pushValue values x) (env 0) := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  rw [same]
  exact L.translation_eval p _ _

theorem compatible_unary (p : V) : N.GroundUnary (fun q => N.Compatible q p) := by
  refine ⟨.ex (.and (L.strengthen (.variable 0) (.variable 1)) (L.strengthen (.variable 0) (.named p))),
    ⟨L.strengthen_scope (Nat.zero_lt_succ _) (Nat.succ_lt_succ (Nat.zero_lt_succ _)),
     L.strengthen_scope (Nat.zero_lt_succ _) trivial⟩, fun env => ?_⟩
  apply exists_congr
  intro r
  exact and_congr (L.strengthen_eval _ _ _) (L.strengthen_eval _ _ _)

theorem below_unary (p : V) : N.GroundUnary (fun q => N.Refines q p) :=
  ⟨L.strengthen (.variable 0) (.named p),L.strengthen_scope (Nat.zero_lt_succ _) trivial,fun env =>
    L.strengthen_eval _ _ env⟩

end OrderForcingLanguage

namespace GenericOrder

variable (G : GenericOrder N) (L : N.OrderForcingLanguage)
include L

/-- Truth in the expanded language is witnessed by one condition of the
generic filter. All dense classes used by the proof have base formulas. -/
theorem forcing_truth (p : Fragment V) {n : Nat} (bound : p.bound n) (values : Nat → V) :
    p.eval N.mem G.order values ↔ ∃ q, G.filter q ∧ N.Forces p q values := by
  classical
  induction p generalizing n values with
  | bot =>
    exact ⟨False.elim,fun ⟨_,_,h⟩ => h⟩
  | eq a b | mem a b =>
    constructor
    · intro h
      obtain ⟨q,hq⟩ := G.inhabited
      exact ⟨q,hq,h⟩
    · exact fun ⟨_,_,h⟩ => h
  | order a b => rfl
  | and a b ia ib =>
    constructor
    · rintro ⟨ha,hb⟩
      obtain ⟨p,hP,fa⟩ := (ia bound.1 values).mp ha
      obtain ⟨q,hQ,fb⟩ := (ib bound.2 values).mp hb
      obtain ⟨r,hR,left,right⟩ := G.directed p q hP hQ
      exact ⟨r,hR,N.force_refines a left values fa,N.force_refines b right values fb⟩
    · rintro ⟨q,hQ,fa,fb⟩
      exact ⟨(ia bound.1 values).mpr ⟨q,hQ,fa⟩,(ib bound.2 values).mpr ⟨q,hQ,fb⟩⟩
  | neg a ih =>
    constructor
    · intro truth
      let decision q := N.Forces a q values ∨ N.Forces (.neg a) q values
      have defn := (L.force_unary a bound values).or (L.force_unary (.neg a) bound values)
      have dense : N.Dense decision := by
        intro q hq
        by_cases sometimes : ∃ r, N.Refines r q ∧ N.Forces a r values
        · obtain ⟨r,extends_,yes⟩ := sometimes
          exact ⟨r,extends_,Or.inl yes⟩
        · exact ⟨q,N.refines_refl hq,Or.inr fun r stronger yes => sometimes ⟨r,stronger,yes⟩⟩
      obtain ⟨q,hq,yes | no⟩ := G.meets decision defn dense
      · exact (truth ((ih bound values).mpr ⟨q,hq,yes⟩)).elim
      · exact ⟨q,hq,no⟩
    · rintro ⟨q,hq,no⟩ yes
      obtain ⟨r,hr,atR⟩ := (ih bound values).mp yes
      obtain ⟨s,_,toQ,toR⟩ := G.directed q r hq hr
      exact no s toQ (N.force_refines a toR values atR)
  | ex a ih =>
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨q,hq,forced⟩ := (ih bound (pushValue values x)).mp hx
      exact ⟨q,hq,fun r stronger => ⟨r,N.refines_refl (N.refines_strong stronger),x,
        N.force_refines a stronger _ forced⟩⟩
    · rintro ⟨q,hq,forced⟩
      let request p := ¬N.Compatible p q ∨ N.Refines p q ∧ ∃ x, N.Forces a p (pushValue values x)
      have description := (L.compatible_unary q).not.or
        ((L.below_unary q).and (L.force_witness a bound values))
      have dense : N.Dense request := by
        intro p hp
        by_cases together : N.Compatible p q
        · obtain ⟨r,toP,toQ⟩ := together
          obtain ⟨s,toR,x,atS⟩ := forced r toQ
          exact ⟨s,N.refines_trans toR toP,Or.inr ⟨N.refines_trans toR toQ,x,atS⟩⟩
        · exact ⟨p,N.refines_refl hp,Or.inl together⟩
      obtain ⟨p,hp,no | yes⟩ := G.meets request description dense
      · obtain ⟨r,_,toP,toQ⟩ := G.directed p q hp hq
        exact (no ⟨r,toP,toQ⟩).elim
      · obtain ⟨_,x,truth⟩ := yes
        exact ⟨x,(ih bound (pushValue values x)).mpr ⟨p,hp,truth⟩⟩

theorem expanded_forcing_truth (p : Expanded.Formula V) {n : Nat}
    (scope : Expanded.Bound p n) (env : Nat → V) :
    Expanded.eval N.mem G.order p env ↔ ∃ q, G.filter q ∧ N.Forces p.fragment q env :=
  (Expanded.fragment_eval N.mem G.order p env).symm.trans
    (G.forcing_truth L p.fragment (Expanded.fragment_scope p scope) env)

end GenericOrder
end PalomarI3380.SquareRepresentation.SetContext
