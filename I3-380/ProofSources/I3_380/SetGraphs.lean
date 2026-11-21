module
public import I3_380.OrdinalOrder
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem at_pair (f x y : V) :
    Internal.At N.mem f x y ↔ N.mem (N.orderedPair x y) f := by
  constructor
  · rintro ⟨p, hp, code⟩
    exact ((N.orderedPair_iff _ _ _).mp code) ▸ hp
  · exact fun h => ⟨_, h, N.orderedPair_intro _ _⟩

private def insertOutput : Nat → Nat
  | 0 => 1
  | 1 => 0
  | i + 2 => i + 3

private theorem insertOutput_bound (arity i : Nat) (h : i < arity + 2) :
    insertOutput i < arity + 3 := by
  cases i with
  | zero => simp [insertOutput]
  | succ i => cases i <;> simp [insertOutput] <;> omega

private theorem insertOutput_env (params : List V) (x y code : V) :
    pushValue (parameterEnv params x code) y ∘ insertOutput = parameterEnv params x y := by
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

/-- Reify the graph of a definable partial function on a given set as a
set of Kuratowski pairs. This is the graph form of Replacement. -/
theorem graph_image (params : List V) {R : (Nat → V) → Prop}
    (described : N.square.Definable (params.length + 2) R)
    (unique : ∀ x y z, R (parameterEnv params x y) → R (parameterEnv params x z) → y = z)
    (domain : V) :
    ∃ graph, (∀ x y, Internal.At N.mem graph x y ↔ N.mem x domain ∧ R (parameterEnv params x y)) ∧
      (∀ p, N.mem p graph → ∃ x y, N.mem x domain ∧ R (parameterEnv params x y) ∧
        p = N.orderedPair x y) := by
  let desc := fun env => ∃ y, R (pushValue env y ∘ insertOutput) ∧
    Internal.OrderedPair N.mem (env 0) y (env 1)
  have definable : N.square.Definable (params.length + 2) desc := by
    exact Definable.ex ((described.reindex (m := params.length + 3) insertOutput (insertOutput_bound params.length)).and
      (Definable.orderedPair (N := N) (i := 1) (j := 0) (k := 2) (by omega) (by omega) (by omega)))
  have descAt (x p : V) : desc (parameterEnv params x p) ↔
      ∃ y, R (parameterEnv params x y) ∧ p = N.orderedPair x y := by
    change (∃ y, R (pushValue (parameterEnv params x p) y ∘ insertOutput) ∧
      Internal.OrderedPair N.mem x y p) ↔ _
    simp only [insertOutput_env, N.orderedPair_iff]
  have outputs (x z₁ z₂ : V) (left : desc (parameterEnv params x z₁))
      (right : desc (parameterEnv params x z₂)) : z₁ = z₂ := by
    obtain ⟨y, hy, rfl⟩ := (descAt _ _).mp left
    obtain ⟨z, hz, rfl⟩ := (descAt _ _).mp right
    rw [unique x y z hy hz]
  obtain ⟨graph, member⟩ := N.image params definable outputs domain
  have exactMembers (p : V) : N.mem p graph ↔
      ∃ x y, N.mem x domain ∧ R (parameterEnv params x y) ∧ p = N.orderedPair x y := by
    rw [member]
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨y, hy, same⟩ := (descAt x p).mp h
      exact ⟨x, y, hx, hy, same⟩
    · rintro ⟨x, y, hx, hy, same⟩
      exact ⟨x, hx, (descAt _ _).mpr ⟨y, hy, same⟩⟩
  refine ⟨graph, fun x y => (N.at_pair _ _ _).trans ((exactMembers _).trans ?_),
    fun p => (exactMembers p).mp⟩
  constructor
  · rintro ⟨i, j, hi, hj, same⟩
    obtain ⟨rfl, rfl⟩ := N.orderedPair_inj same
    exact ⟨hi, hj⟩
  · exact fun h => ⟨x, y, h.1, h.2, rfl⟩

theorem functionOf (params : List V) {R : (Nat → V) → Prop}
    (described : N.square.Definable (params.length + 2) R)
    (unique : ∀ x y z, R (parameterEnv params x y) → R (parameterEnv params x z) → y = z)
    (domain : V) (total : ∀ x, N.mem x domain → ∃ y, R (parameterEnv params x y)) :
    ∃ graph, Internal.FunctionOn N.mem graph domain ∧
      ∀ x y, Internal.At N.mem graph x y ↔ N.mem x domain ∧ R (parameterEnv params x y) := by
  obtain ⟨g, value, shaped⟩ := N.graph_image params described unique domain
  refine ⟨g, ⟨?_, ?_⟩, value⟩
  · intro x hx
    obtain ⟨y, hy⟩ := total x hx
    exact ⟨y, (value x y).mpr ⟨hx, hy⟩, fun z hz => unique x z y ((value x z).mp hz).2 hy⟩
  · intro p hp
    obtain ⟨x, y, hx, _, same⟩ := shaped p hp
    exact ⟨x, y, hx, (N.orderedPair_iff _ _ _).mpr same⟩

theorem functionOn_value {f domain x : V} (hf : Internal.FunctionOn N.mem f domain) (hx : N.mem x domain) :
    ∃ y, Internal.At N.mem f x y ∧ (∀ z, Internal.At N.mem f x z → z = y) := hf.1 x hx

theorem function_ext {f g domain : V}
    (hf : Internal.FunctionOn N.mem f domain) (hg : Internal.FunctionOn N.mem g domain)
    (same : ∀ x y, N.mem x domain → (Internal.At N.mem f x y ↔ Internal.At N.mem g x y)) :
    f = g := by
  apply N.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, code⟩ := hf.2 p hp
    have pEq := (N.orderedPair_iff _ _ _).mp code
    subst p
    exact (N.at_pair _ _ _).mp ((same x y hx).mp ⟨_, hp, code⟩)
  · intro hp
    obtain ⟨x, y, hx, code⟩ := hg.2 p hp
    have pEq := (N.orderedPair_iff _ _ _).mp code
    subst p
    exact (N.at_pair _ _ _).mp ((same x y hx).mpr ⟨_, hp, code⟩)

end PalomarI3380.SquareRepresentation.SetContext
