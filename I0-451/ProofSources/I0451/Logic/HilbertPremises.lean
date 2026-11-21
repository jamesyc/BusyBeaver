module
public import I0451.Logic.ImplicationBasis

/-! Derive the usual propositional rules from the literal AX head.
Premises are a proof convenience. Discharge eliminates them using only
detachment and the verified implicational basis. -/
@[expose] public section
namespace I0451.Logic

variable {α : Type} {P : α → Prop} {arrow : α → α → α}

local infixr:55 " ⟹ " => arrow

inductive WithPremises (P : α → Prop) (arrow : α → α → α) (context : List α) : α → Prop
  | premise {a} : a ∈ context → WithPremises P arrow context a
  | known {a} : P a → WithPremises P arrow context a
  | detach {a b} : WithPremises P arrow context a → WithPremises P arrow context (arrow a b) →
      WithPremises P arrow context b

namespace WithPremises

theorem weaken {context larger : List α} {f : α} (derived : WithPremises P arrow context f)
    (included : ∀ x ∈ context, x ∈ larger) : WithPremises P arrow larger f := by
  induction derived with
  | premise member => exact .premise (included _ member)
  | known proof => exact .known proof
  | detach _ _ ihA ihB => exact .detach ihA ihB

theorem closed {f : α} (derived : WithPremises P arrow [] f)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b) : P f := by
  induction derived with
  | premise member => simp at member
  | known proof => exact proof
  | detach _ _ ihA ihB => exact mp ihA ihB

theorem reflexive (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b) (a : α) : P (a ⟹ a) :=
  mp (basis.weakening a a) (mp (basis.weakening a (a ⟹ a)) (basis.distribution a (a ⟹ a) a))

theorem discharge (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b)
    {context : List α} {a f : α} (derived : WithPremises P arrow (a :: context) f) :
    WithPremises P arrow context (a ⟹ f) := by
  induction derived with
  | @premise f member =>
    rcases List.mem_cons.mp member with rfl | inContext
    · exact .known (reflexive basis mp _)
    · exact .detach (.premise inContext) (.known (basis.weakening f a))
  | @known f proof =>
    exact .detach (.known proof) (.known (basis.weakening f a))
  | @detach u v _ _ ihA ihB =>
    exact .detach ihA (.detach ihB (.known (basis.distribution a u v)))

theorem doubleNegation (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b)
    (bot : α) (explode : ∀ a, P (bot ⟹ a)) (a : α) :
    P (((a ⟹ bot) ⟹ bot) ⟹ a) := by
  apply WithPremises.closed _ mp
  apply discharge basis mp
  refine .detach (discharge basis mp ?_) (.known (basis.peirce a bot))
  have hypothetical := WithPremises.premise (P := P) (arrow := arrow) (context := [a ⟹ bot, (a ⟹ bot) ⟹ bot])
    (a := a ⟹ bot) (by simp)
  have contradiction := WithPremises.premise (P := P) (arrow := arrow)
    (context := [a ⟹ bot, (a ⟹ bot) ⟹ bot]) (a := (a ⟹ bot) ⟹ bot) (by simp)
  exact .detach (.detach hypothetical contradiction) (.known (explode a))

theorem conjunction_left (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b)
    (bot : α) (explode : ∀ a, P (bot ⟹ a)) (a b : α) :
    P (((a ⟹ b ⟹ bot) ⟹ bot) ⟹ a) := by
  apply WithPremises.closed _ mp
  apply discharge basis mp
  refine .detach (discharge basis mp ?_) (.known (doubleNegation basis mp bot explode a))
  refine .detach (discharge basis mp (a := a) ?_) (.premise (a := (a ⟹ b ⟹ bot) ⟹ bot) (by simp))
  have contra : WithPremises P arrow [a, a ⟹ bot, (a ⟹ b ⟹ bot) ⟹ bot] bot :=
    .detach (.premise (a := a) (by simp)) (.premise (by simp))
  exact .detach contra (.known (explode (b ⟹ bot)))

theorem conjunction_right (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b)
    (bot : α) (explode : ∀ a, P (bot ⟹ a)) (a b : α) :
    P (((a ⟹ b ⟹ bot) ⟹ bot) ⟹ b) := by
  apply WithPremises.closed _ mp
  apply discharge basis mp
  refine .detach (discharge basis mp ?_) (.known (doubleNegation basis mp bot explode b))
  refine .detach ?_ (.premise (a := (a ⟹ b ⟹ bot) ⟹ bot) (by simp))
  exact .detach (.premise (by simp)) (.known (basis.weakening (b ⟹ bot) a))

theorem conjunction_intro (basis : ImplicationBasis (P := P) arrow)
    (mp : ∀ {a b}, P a → P (a ⟹ b) → P b) (bot a b : α) :
    P (a ⟹ b ⟹ (a ⟹ b ⟹ bot) ⟹ bot) := by
  apply WithPremises.closed _ mp
  apply discharge basis mp
  apply discharge basis mp
  apply discharge basis mp
  exact .detach (.premise (a := b) (by simp))
    (.detach (.premise (a := a) (by simp)) (.premise (by simp)))

end WithPremises

namespace Derives

variable {foundation berkeley : Nat}

theorem explode (a : Nat) : Derives foundation berkeley (imp 1 a) := by
  have quantified : Derives foundation berkeley (imp (ex 0 (all 0 a)) a) :=
    .head 0 a 0 0 _ (by simp [heads])
  have before : Derives foundation berkeley (imp 1 (ex 0 (all 0 a))) :=
    (implicationBasis foundation berkeley).weakening 1 (all 0 (neg (all 0 a)))
  exact .mp quantified (.mp before
    ((implicationBasis foundation berkeley).syllogism 1 (ex 0 (all 0 a)) a))

theorem and_left {a b : Nat} (derived : Derives foundation berkeley (Logic.and a b)) :
    Derives foundation berkeley a :=
  .mp derived (WithPremises.conjunction_left (implicationBasis foundation berkeley)
    (fun x y => .mp x y) 1 explode a b)

theorem and_right {a b : Nat} (derived : Derives foundation berkeley (Logic.and a b)) :
    Derives foundation berkeley b :=
  .mp derived (WithPremises.conjunction_right (implicationBasis foundation berkeley)
    (fun x y => .mp x y) 1 explode a b)

theorem and_intro {a b : Nat} (left : Derives foundation berkeley a) (right : Derives foundation berkeley b) :
    Derives foundation berkeley (Logic.and a b) :=
  .mp right (.mp left (WithPremises.conjunction_intro (implicationBasis foundation berkeley)
    (fun x y => .mp x y) 1 a b))

theorem vacuity_mem {a b c : Nat} (notLeft : c ≠ a) (notRight : c ≠ b) :
    Derives foundation berkeley (imp (mem a b) (all c (mem a b))) :=
  (Derives.bundle a b c notLeft notRight).and_right.and_right.and_left.and_left

theorem vacuity_eq {a b c : Nat} (notLeft : c ≠ a) (notRight : c ≠ b) :
    Derives foundation berkeley (imp (equal a b) (all c (equal a b))) :=
  (Derives.bundle a b c notLeft notRight).and_right.and_right.and_left.and_right

end Derives

end I0451.Logic
