module
public import I3_380.SquareProjections
public import I3_380.Logic.Syntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.QuasiProjections

open PalomarI3380.Logic (pushValue)

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}
variable (P : QuasiProjections S)

/-- Nested pairs represent a finite initial interval of an assignment. -/
def Encodes (P : QuasiProjections S) : Nat → Point → (Nat → Point) → Prop
  | 0, _, _ => True
  | n + 1, code, env =>
    S.rel P.first code (env 0) ∧
      ∃ tail, S.rel P.second code tail ∧ P.Encodes n tail (fun i => env (i + 1))

theorem push_encoding {n : Nat} {t : Point} {env : Nat → Point}
    (encoded : P.Encodes n t env) {x code : Point}
    (head : S.rel P.first code x) (tail : S.rel P.second code t) :
    P.Encodes (n + 1) code (pushValue env x) :=
  ⟨head, t, tail, encoded⟩

theorem encoding_exists (n : Nat) (env : Nat → Point) : ∃ code, P.Encodes n code env := by
  induction n generalizing env with
  | zero => exact ⟨env 0, trivial⟩
  | succ n ih =>
    obtain ⟨tail, encoded⟩ := ih (fun i => env (i + 1))
    obtain ⟨code, hp, hs⟩ := P.pair (env 0) tail
    exact ⟨code, hp, tail, hs, encoded⟩

def projection (P : QuasiProjections S) : Nat → A
  | 0 => P.first
  | i + 1 => M.product P.second (P.projection i)

theorem projection_value {n i : Nat} {code : Point} {env : Nat → Point}
    (hEnc : P.Encodes n code env) (hi : i < n) (x : Point) :
    S.rel (P.projection i) code x ↔ x = env i := by
  induction i generalizing n code env with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      have hFirst : S.rel P.first code (env 0) := hEnc.1
      exact ⟨fun h => P.firstFunction _ _ _ h hFirst, fun eq => eq.symm ▸ hFirst⟩
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨_, tail, ht, hNext⟩ := hEnc
      change S.rel (M.product P.second (P.projection i)) code x ↔ x = env (i + 1)
      rw [S.product]
      have projection := ih hNext (by omega)
      constructor
      · rintro ⟨newTail, same, h⟩
        have eq := P.secondFunction _ _ _ same ht
        exact projection.mp (eq ▸ h)
      · intro eq
        exact ⟨tail, ht, projection.mpr eq⟩

/-- The diagonal of codes for an assignment with the specified arity. -/
def tupleDomain (P : QuasiProjections S) : Nat → A
  | 0 => M.constant .I
  | n + 1 => M.inf (domain M P.first) (domain M (M.product P.second (P.tupleDomain n)))

theorem tuple_domain (n : Nat) (x y : Point) :
    S.rel (P.tupleDomain n) x y ↔ x = y ∧ ∃ env, P.Encodes n x env := by
  induction n generalizing x y with
  | zero =>
    exact (S.identity x y).trans ⟨fun h => ⟨h, fun _ => x, trivial⟩, And.left⟩
  | succ n ih =>
    change S.rel (M.neg (M.nand (domain M P.first)
      (domain M (M.product P.second (P.tupleDomain n))))) x y ↔ _
    simp only [S.meet, S.domain_iff, S.product]
    constructor
    · rintro ⟨⟨eq, head, hh⟩, ⟨_, _, tail, ht, valid⟩⟩
      have ⟨_, values, hValues⟩ := (ih _ _).mp valid
      exact ⟨eq, pushValue values head, P.push_encoding hValues hh ht⟩
    · rintro ⟨eq, env, head, tail, ht, hValues⟩
      exact ⟨⟨eq, env 0, head⟩, ⟨eq, tail, tail, ht, (ih _ _).mpr ⟨rfl, _, hValues⟩⟩⟩

def within (P : QuasiProjections S) (n : Nat) (r : A) : A :=
  M.inf (P.tupleDomain n) r

theorem within_rel {n : Nat} {r : A} {x y : Point} :
    S.rel (P.within n r) x y ↔ S.rel (P.tupleDomain n) x y ∧ S.rel r x y :=
  S.meet _ _ x y

theorem within_code {n : Nat} {r : A} {x : Point} {env : Nat → Point}
    (enc : P.Encodes n x env) : S.rel (P.within n r) x x ↔ S.rel r x x := by
  rw [P.within_rel]
  exact ⟨And.right, fun h => ⟨(P.tuple_domain n x x).mpr ⟨rfl, env, enc⟩, h⟩⟩

/-- Project a truth diagonal for extended assignments to the older assignment. -/
def project (P : QuasiProjections S) (r : A) : A :=
  domain M (M.converse (M.product r P.second))

theorem project_at {r : A} {n : Nat} {t : Point} {env : Nat → Point}
    (enc : P.Encodes n t env)
    (inDomain : ∀ x y, S.rel r x y → S.rel (P.tupleDomain (n + 1)) x y)
    (description : (Nat → Point) → Prop)
    (accurate : ∀ (code : Point) (values : Nat → Point), P.Encodes (n + 1) code values →
      (S.rel r code code ↔ description values)) :
    S.rel (P.project r) t t ↔ ∃ x, description (pushValue env x) := by
  change S.rel (domain M (M.converse (M.product r P.second))) t t ↔ _
  simp only [S.domain_iff, S.converse, S.product, true_and]
  constructor
  · rintro ⟨code, next, hTruth, hNext⟩
    obtain ⟨eq, values, hValues⟩ := (P.tuple_domain (n + 1) code next).mp (inDomain _ _ hTruth)
    subst next
    have hHead : S.rel P.first code (values 0) := hValues.1
    exact ⟨values 0, (accurate code _ (P.push_encoding enc hHead hNext)).mp hTruth⟩
  · rintro ⟨x, hx⟩
    obtain ⟨code, head, tail⟩ := P.pair x t
    exact ⟨code, code, (accurate code _ (P.push_encoding enc head tail)).mpr hx, tail⟩

end PalomarI3380.SquareRepresentation.QuasiProjections
