module
public import I0451.Logic.Derivability

/-! The eighth AX head derives the Tarski–Bernays implicational basis.
The proof follows Meredith and Prior's detachment proof, reproduced as
Figure 6 of Wernhard and Bibel, DOI 10.1007/s10817-024-09711-8.
The argument is uniform in the code domain and the implication constructor. -/
@[expose] public section
namespace I0451.Logic

variable {α : Type} {P : α → Prop} (arrow : α → α → α)

local infixr:55 " ⟹ " => arrow

structure ImplicationBasis : Prop where
  syllogism : ∀ a b c, P ((a ⟹ b) ⟹ (b ⟹ c) ⟹ a ⟹ c)
  peirce : ∀ a b, P (((a ⟹ b) ⟹ a) ⟹ a)
  weakening : ∀ a b, P (a ⟹ b ⟹ a)
  exchange : ∀ a b c, P ((a ⟹ b ⟹ c) ⟹ b ⟹ a ⟹ c)
  contraction : ∀ a b, P ((a ⟹ a ⟹ b) ⟹ a ⟹ b)
  distribution : ∀ a b c, P ((a ⟹ b ⟹ c) ⟹ (a ⟹ b) ⟹ a ⟹ c)

/-- Meredith and Prior's detachment proof specialized to an arbitrary
implication constructor. References to earlier lemmas are kept shared. -/
theorem implicationBasis_of_single
    (detach : ∀ {a b}, P a → P (a ⟹ b) → P b)
    (single : ∀ a b c d, P (((a ⟹ b) ⟹ c) ⟹ (c ⟹ a) ⟹ d ⟹ a)) :
    ImplicationBasis (P := P) arrow := by
  have m2 (a b c : α) : P (((a ⟹ b) ⟹ a) ⟹ c ⟹ a) := by
    let result := ((a ⟹ b) ⟹ a) ⟹ c ⟹ a
    let diagonal := a ⟹ a
    let reflexive := (diagonal ⟹ a) ⟹ diagonal ⟹ diagonal
    have premise := detach (single a b (a ⟹ b) c)
      (single (a ⟹ b) (a ⟹ b) result diagonal)
    have collapse := detach premise (single result (a ⟹ b) (diagonal ⟹ a ⟹ b) reflexive)
    exact detach (single a a a a) (detach (single a a (a ⟹ b) c) collapse)
  have m3 (a b c : α) : P (((a ⟹ b) ⟹ c) ⟹ b ⟹ c) := by
    let result := ((a ⟹ b) ⟹ c) ⟹ b ⟹ c
    let diagonal := a ⟹ a
    let reflexive := (diagonal ⟹ a) ⟹ diagonal ⟹ diagonal
    have premise := detach (m2 b c a) (single (b ⟹ c) b (a ⟹ b) ((a ⟹ b) ⟹ c))
    have second := detach premise (single (a ⟹ b) (b ⟹ c) result (c ⟹ a))
    have collapse := detach second (single result (a ⟹ b) ((c ⟹ a) ⟹ a ⟹ b) reflexive)
    exact detach (single a a a a) (detach (single c a (a ⟹ b) b) collapse)
  have m4 (a b c : α) : P (a ⟹ (a ⟹ b) ⟹ c ⟹ b) :=
    detach (single b a a c) (m3 (b ⟹ a) a ((a ⟹ b) ⟹ c ⟹ b))
  have m5 (a b c d e : α) : P (((a ⟹ b) ⟹ c ⟹ d) ⟹ ((b ⟹ e) ⟹ d) ⟹ c ⟹ d) := by
    let trigger := (b ⟹ e) ⟹ d
    let middle := trigger ⟹ c ⟹ d
    let result := ((a ⟹ b) ⟹ c ⟹ d) ⟹ middle
    let diagonal := a ⟹ a
    let reflexive := (diagonal ⟹ a) ⟹ diagonal ⟹ diagonal
    have first := detach (m4 (b ⟹ e) d c) (single b e middle a)
    have second := detach first (single middle b (a ⟹ b) ((a ⟹ b) ⟹ c ⟹ d))
    have third := detach second (single (a ⟹ b) middle result ((c ⟹ d) ⟹ a))
    have collapse := detach third (single result (a ⟹ b) (((c ⟹ d) ⟹ a) ⟹ a ⟹ b) reflexive)
    exact detach (single a a a a) (detach (single (c ⟹ d) a (a ⟹ b) trigger) collapse)
  have m6 (a b c d : α) : P (((a ⟹ b) ⟹ c ⟹ d) ⟹ (a ⟹ d) ⟹ c ⟹ d) :=
    detach (single d a a c) (m5 (d ⟹ a) a (a ⟹ d) (c ⟹ d) b)
  have m7 (a b c d : α) : P ((a ⟹ b ⟹ c) ⟹ ((a ⟹ d) ⟹ c) ⟹ b ⟹ c) :=
    detach (m4 (a ⟹ d) c b) (m6 a d ((a ⟹ d) ⟹ c) (b ⟹ c))
  have m8 (a b c d e : α) : P (((((a ⟹ b) ⟹ c) ⟹ d) ⟹ e ⟹ a) ⟹ (c ⟹ a) ⟹ e ⟹ a) :=
    detach (single a b c e) (m7 ((a ⟹ b) ⟹ c) (c ⟹ a) (e ⟹ a) d)
  have m9 (a b : α) : P ((a ⟹ b) ⟹ a ⟹ b) :=
    detach (m3 (b ⟹ a) a b) (m8 b a a b a)
  have m10 (a b c d e f : α) :
      P ((((a ⟹ b) ⟹ c ⟹ b) ⟹ ((b ⟹ d) ⟹ a) ⟹ e) ⟹ f ⟹ ((b ⟹ d) ⟹ a) ⟹ e) :=
    detach (m8 b d a e c) (single (((b ⟹ d) ⟹ a) ⟹ e) (c ⟹ b) ((a ⟹ b) ⟹ c ⟹ b) f)
  have m11 (a b c d e : α) : P ((((a ⟹ b) ⟹ c) ⟹ d ⟹ b) ⟹ ((b ⟹ e) ⟹ d) ⟹ a ⟹ b) := by
    let diagonal := a ⟹ a
    let reflexive := (diagonal ⟹ a) ⟹ diagonal ⟹ diagonal
    let result := ((b ⟹ e) ⟹ d) ⟹ a ⟹ b
    have collapse := detach (m10 d b a e (a ⟹ b) (((a ⟹ b) ⟹ c) ⟹ d ⟹ b))
      (m10 (d ⟹ b) (a ⟹ b) ((b ⟹ e) ⟹ d) c result reflexive)
    exact detach (single a a a a) collapse
  have m12 (a b c d e : α) : P ((((a ⟹ b) ⟹ c) ⟹ d ⟹ b) ⟹ ((b ⟹ e) ⟹ a) ⟹ d ⟹ b) :=
    detach (m11 d b a a e) (m5 ((d ⟹ b) ⟹ a) (a ⟹ b) ((b ⟹ e) ⟹ a) (d ⟹ b) c)
  have m13 (a b c d : α) : P ((((a ⟹ b) ⟹ c) ⟹ d) ⟹ (d ⟹ b) ⟹ a ⟹ b) :=
    detach (m6 d (a ⟹ b) a b) (m12 d (a ⟹ b) (a ⟹ b) (d ⟹ b) c)
  have m14 (a b c : α) : P (((a ⟹ b) ⟹ c) ⟹ (c ⟹ a) ⟹ a) :=
    detach (m9 (c ⟹ a) a) (m12 c a a (c ⟹ a) b)
  have m15 (a b : α) : P (a ⟹ (a ⟹ b) ⟹ b) :=
    detach (m14 b a a) (m3 (b ⟹ a) a ((a ⟹ b) ⟹ b))
  have m16 (a b c : α) : P ((a ⟹ b) ⟹ ((a ⟹ c) ⟹ b) ⟹ b) :=
    detach (m15 (a ⟹ c) b) (m6 a c ((a ⟹ c) ⟹ b) b)
  have syllogism (a b c : α) : P ((a ⟹ b) ⟹ (b ⟹ c) ⟹ a ⟹ c) := by
    let step := ((a ⟹ c) ⟹ b) ⟹ b
    let rest := (b ⟹ c) ⟹ a ⟹ c
    have combine := detach (m16 a b c) (m16 (a ⟹ b) step rest)
    exact detach (m13 a c b b) (detach combine (m13 (a ⟹ b) rest step step))
  have peirce (a b : α) : P (((a ⟹ b) ⟹ a) ⟹ a) :=
    detach (m9 a b) (m14 a b (a ⟹ b))
  have weakening (a b : α) : P (a ⟹ b ⟹ a) :=
    detach (m3 a b a) (m3 (a ⟹ b) a (b ⟹ a))
  have contraction (a b : α) : P ((a ⟹ a ⟹ b) ⟹ a ⟹ b) :=
    detach (peirce a b) (m14 (a ⟹ b) a a)
  have exchange (a b c : α) : P ((a ⟹ b ⟹ c) ⟹ b ⟹ a ⟹ c) := by
    have convert := detach (m6 b (a ⟹ c) a c) (m11 b (a ⟹ c) (a ⟹ c) (b ⟹ c) c)
    exact detach convert (detach (m7 a b c c) (syllogism (a ⟹ b ⟹ c) _ (b ⟹ a ⟹ c)))
  have lift {a b c : α} (h : P (b ⟹ c)) : P ((a ⟹ b) ⟹ a ⟹ c) :=
    detach h (detach (syllogism a b c) (exchange (a ⟹ b) (b ⟹ c) (a ⟹ c)))
  refine ⟨syllogism, peirce, weakening, exchange, contraction, ?_⟩
  intro a b c
  have composition := detach (syllogism a b c) (exchange (a ⟹ b) (b ⟹ c) (a ⟹ c))
  have first := lift (a := a) composition
  have second := detach (exchange a (a ⟹ b) (a ⟹ c)) (detach first (syllogism _ _ _))
  have third := lift (a := a ⟹ b) (contraction a c)
  exact detach third (detach second (syllogism _ _ _))

theorem Derives.implicationBasis (f b : Nat) : ImplicationBasis (P := Derives f b) imp :=
  implicationBasis_of_single imp (fun ha hab => .mp ha hab) fun a x c d =>
    .head c d a x _ (by simp [heads])

end I0451.Logic
