module
public import I3_380.SquareDefinability
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic (pushValue)
open RelationFormula

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

def agreesAt (values : List Point) (offset : Nat) (env : Nat → Point) : Prop :=
  ∀ i, (hi : i < values.length) → env (offset + i) = values[i]

theorem agreesAt_cons {value : Point} {values : List Point} {offset : Nat} {env : Nat → Point} :
    agreesAt (value :: values) offset env ↔ env offset = value ∧ agreesAt values (offset + 1) env := by
  constructor
  · intro h
    have head := h 0 (by simp)
    change env (offset + 0) = value at head
    refine ⟨by simpa only [Nat.add_zero] using head, ?_⟩
    intro i hi
    have eq := h (i + 1) (by simp only [List.length_cons]; omega)
    simpa only [List.getElem_cons_succ, show offset + (i + 1) = offset + 1 + i by omega] using eq
  · rintro ⟨head, tail⟩ i hi
    cases i with
    | zero => simpa
    | succ i =>
      have eq := tail i (by simp only [List.length_cons] at hi; omega)
      simpa only [List.getElem_cons_succ, show offset + (i + 1) = offset + 1 + i by omega] using eq

/-- Fix all named parameters at their variable positions in a tuple. -/
theorem named_parameters (P : QuasiProjections S) (names : ∀ p, S.Named p)
    (values : List Point) (offset depth : Nat) (bound : offset + values.length ≤ depth) :
    ∃ a, ∀ code env, P.Encodes depth code env →
      (S.rel a code code ↔ agreesAt values offset env) := by
  induction values generalizing offset with
  | nil =>
    exact ⟨M.constant .I, fun code env _ =>
      ⟨fun _ i hi => by simp at hi, fun _ => (S.identity code code).mpr rfl⟩⟩
  | cons value values ih =>
    have inRange : offset < depth := by simp only [List.length_cons] at bound; omega
    obtain ⟨named, name⟩ := names value
    obtain ⟨tail, hTail⟩ := ih (offset + 1) (by simp only [List.length_cons] at bound; omega)
    let head := domain M (M.product (P.projection offset) named)
    refine ⟨M.inf head tail, fun code env enc => ?_⟩
    have hHead : S.rel head code code ↔ env offset = value := by
      change S.rel (domain M (M.product (P.projection offset) named)) code code ↔ _
      simp only [S.domain_iff, S.product, P.projection_value enc inRange, name, true_and]
      constructor
      · rintro ⟨_, _, rfl, h, _⟩
        exact h
      · intro eq
        exact ⟨value, env offset, rfl, eq, rfl⟩
    exact (S.meet _ _ _ _).trans ((and_congr hHead (hTail code env enc)).trans agreesAt_cons.symm)

def parameterEnv {Point : Type} (params : List Point) (x y : Point) : Nat → Point :=
  pushValue (pushValue (fun i => params[i]?.getD x) y) x

theorem parameterEnv_agrees {Point : Type} (params : List Point) (x y : Point) :
    agreesAt params 2 (parameterEnv params x y) := by
  intro i hi
  rw [show 2 + i = i + 1 + 1 by omega]
  change (params[i]?.getD x) = params[i]
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem parameterEnv_unique {Point : Type} (params : List Point) (x y : Point) (env : Nat → Point)
    (head : env 0 = x) (second : env 1 = y) (variables : agreesAt params 2 env) :
    ∀ i, i < params.length + 2 → env i = parameterEnv params x y i := by
  intro i hi
  cases i with
  | zero => exact head
  | succ i =>
    cases i with
    | zero => exact second
    | succ i =>
      have index : i < params.length := by omega
      have same := variables i index
      rw [show 2 + i = i + 1 + 1 by omega] at same
      change env (i + 1 + 1) = params[i]?.getD x
      rwa [List.getElem?_eq_getElem index]

/-- Every binary first-order definition with point parameters is a
represented relation. This includes definitions using extra algebra relations. -/
theorem represented_binary (P : QuasiProjections S) (names : ∀ p, S.Named p)
    (params : List Point) (formula : RelationFormula A) (bound : formula.Bound (params.length + 2)) :
    ∃ r, ∀ x y, S.rel r x y ↔ eval S formula (parameterEnv params x y) := by
  let depth := params.length + 2
  obtain ⟨restrictions, fixed⟩ := named_parameters P names params 2 depth (by dsimp [depth]; omega)
  let actual := truth P depth formula
  let test := M.inf actual restrictions
  let graph := M.product (M.product (M.converse (P.projection 0)) test) (P.projection 1)
  refine ⟨graph, fun x y => ?_⟩
  change S.rel (M.product (M.product (M.converse (P.projection 0))
    (M.neg (M.nand actual restrictions))) (P.projection 1)) x y ↔ _
  simp only [S.product, S.converse, S.meet]
  have h0 : 0 < depth := by dsimp [depth]; omega
  have h1 : 1 < depth := by dsimp [depth]; omega
  constructor
  · rintro ⟨dest, ⟨src, first, holds, fixedParams⟩, second⟩
    have valid := truth_domain P depth formula holds
    obtain ⟨eq, env, enc⟩ := (P.tuple_domain depth src dest).mp valid
    subst dest
    have firstValue := (P.projection_value enc h0 x).mp first
    have secondValue := (P.projection_value enc h1 y).mp second
    have described := (truth_correct P formula bound enc).mp holds
    have same := parameterEnv_unique params x y env firstValue.symm secondValue.symm
      ((fixed src env enc).mp fixedParams)
    exact (eval_congr formula bound env _ same).mp described
  · intro holds
    let env := parameterEnv params x y
    obtain ⟨code, enc⟩ := P.encoding_exists depth env
    exact ⟨code, ⟨code, (P.projection_value enc h0 x).mpr rfl,
      (truth_correct P formula bound enc).mpr holds,
      (fixed code env enc).mpr (parameterEnv_agrees params x y)⟩,
      (P.projection_value enc h1 y).mpr rfl⟩

/-- Exact images of definable partial functions, also with named binary
relations in the language. -/
theorem definable_image (P : QuasiProjections S) (hM : M.Models Manifest.preceding)
    (names : ∀ p, S.Named p) (params : List Point) (formula : RelationFormula A)
    (bound : formula.Bound (params.length + 2))
    (functional : ∀ x y z, eval S formula (parameterEnv params x y) →
      eval S formula (parameterEnv params x z) → y = z)
    (domainSet : Point) :
    ∃ image, ∀ y, S.rel (M.constant .E) y image ↔
      ∃ x, S.rel (M.constant .E) x domainSet ∧ eval S formula (parameterEnv params x y) := by
  obtain ⟨r, description⟩ := represented_binary P names params formula bound
  obtain ⟨image, actual⟩ := S.exact_image_of_functional hM r
    (fun x y z hy hz => functional x y z ((description x y).mp hy) ((description x z).mp hz)) domainSet
  exact ⟨image, fun y => (actual y).trans (exists_congr fun x => and_congr_right fun _ => description x y)⟩

end PalomarI3380.SquareRepresentation
