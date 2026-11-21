module
import Std
@[expose] public section

namespace PalomarI3380

structure MeredithLaws {A : Type} (meet : A → A → A) (neg : A → A) : Prop where
  involution : ∀ x, neg (neg x) = x
  idempotent : ∀ x, meet x x = x
  commutative : ∀ x y, meet x y = meet y x
  associative : ∀ x y z, meet (meet x y) z = meet x (meet y z)
  complement_meet : ∀ x y, meet (neg (meet x y)) x = meet (neg y) x
  absorption : ∀ x y, meet x (neg (meet (neg x) y)) = x

/-- Equational consequences of the Meredith basis. The calculation follows
Truszkowska and Grabowski, ROBBINS2, Lm4. -/
theorem meredithLaws {A : Type} (meet : A → A → A) (neg : A → A)
    (b1 : ∀ x y, meet (neg (meet (neg x) y)) x = x)
    (b2 : ∀ x y z, meet (neg (meet (neg x) y)) (meet z y) = meet y (meet z x)) :
    MeredithLaws meet neg := by
  have absorbNeg (a b : A) : meet (neg a) (meet (neg a) b) = meet (neg a) b := by
    have h := b1 (meet (neg a) b) a
    rw [b1 a b] at h
    exact h
  have exchange (a b : A) : meet (neg (meet (neg a) b)) b = meet b a := by
    have h := b2 a b (neg (meet (neg a) b))
    rw [← absorbNeg (meet (neg a) b) b, h, b1 a b]
  have idem (a : A) : meet a a = a := (exchange a a).symm.trans (b1 a a)
  have absorbLeft (a b : A) : meet a (meet a b) = meet a b := by
    rw [← b2 b a a, idem a, exchange b a]
  have absorbRight (a b : A) : meet (meet a b) b = meet a b := by
    calc
      meet (meet a b) b = meet (neg (meet (neg b) (meet a b))) (meet a b) :=
        (exchange b (meet a b)).symm
      _ = meet (neg (meet (neg b) (meet a b))) (meet a (meet a b)) := by
        rw [absorbLeft a b]
      _ = meet (meet a b) (meet a b) := b2 b (meet a b) a
      _ = meet a b := idem _
  have absorbFirst (a b : A) : meet (meet a b) a = meet a b := by
    rw [← exchange b a, absorbRight]
  have absorbLast (a b : A) : meet a (meet b a) = meet b a := by
    calc
      meet a (meet b a) = meet a (meet b (meet b a)) := by rw [absorbLeft]
      _ = meet (neg (meet (neg (meet b a)) a)) (meet b a) :=
        (b2 (meet b a) a b).symm
      _ = meet b a := b1 _ _
  have absorbComplement (a b : A) : meet (neg (meet a (neg b))) b = b := by
    have h := b1 b (meet a (neg b))
    rwa [absorbLast (neg b) a] at h
  have doubleLeft (a : A) : meet (neg (neg a)) a = a := by
    have h := b1 a (neg a)
    rwa [idem (neg a)] at h
  have doubleRight (a : A) : meet a (neg (neg a)) = a := by
    calc
      meet a (neg (neg a)) = meet (meet (neg (neg a)) a) (neg (neg a)) := by
        rw [doubleLeft]
      _ = meet (neg (neg a)) a := absorbFirst _ _
      _ = a := doubleLeft _
  have doubleInner (a b : A) : meet a (meet (neg (neg a)) b) = meet a b := by
    rw [← b2 b a (neg (neg a)), doubleLeft, exchange]
  have triple (a : A) : neg (neg (neg a)) = neg a := by
    have h : meet a (neg (neg (neg (neg a)))) = a := by
      calc
        meet a (neg (neg (neg (neg a)))) =
            meet a (meet (neg (neg a)) (neg (neg (neg (neg a))))) :=
          (doubleInner _ _).symm
        _ = a := by rw [doubleRight, doubleRight]
    calc
      neg (neg (neg a)) =
          meet (neg (meet a (neg (neg (neg (neg a)))))) (neg (neg (neg a))) :=
        (absorbComplement _ _).symm
      _ = neg a := by rw [h, doubleRight]
  have exchangeTwice (a b : A) :
      meet (neg (meet (neg a) b)) (meet (neg (meet (neg a) b)) b) = meet b a := by
    rw [b2, b1]
  have removeDouble (a b : A) : meet a (neg (neg b)) = meet a b := by
    calc
      meet a (neg (neg b)) =
          meet (neg (meet (neg (neg (neg b))) a))
            (meet (neg (meet (neg (neg (neg b))) a)) a) := (exchangeTwice _ _).symm
      _ = meet a b := by rw [triple, exchangeTwice]
  have inv (x : A) : neg (neg x) = x := by
    calc
      neg (neg x) = meet (neg (meet (neg (neg (neg x))) (neg (neg x)))) (neg (neg x)) :=
        (b1 _ _).symm
      _ = x := by rw [triple, removeDouble, removeDouble, b1]
  have absorbFirstNeg (a b : A) : meet a (neg (meet (neg a) b)) = a := by
    let t := neg (meet (neg a) b)
    calc
      meet a t = meet (meet t a) t := by rw [b1]
      _ = meet t a := absorbFirst t a
      _ = a := b1 a b
  have absorbLastNeg (a b : A) : meet a (neg (meet b (neg a))) = a := by
    let t := neg (meet b (neg a))
    calc
      meet a t = meet (meet t a) t := by rw [absorbComplement]
      _ = meet t a := absorbFirst t a
      _ = a := absorbComplement b a
  have absorbNegLeft (a b : A) : meet (neg a) (neg (meet a b)) = neg a := by
    simpa only [inv] using absorbFirstNeg (neg a) b
  have absorbNegRight (a b : A) : meet (neg a) (neg (meet b a)) = neg a := by
    simpa only [inv] using absorbLastNeg (neg a) b
  have exchangeNested (a b z : A) :
      let t := neg (meet (neg (meet b a)) z)
      meet (neg (meet (neg a) t)) (meet b t) = meet b a := by
    dsimp only
    rw [b2, b1]
  have commNeg (a b : A) : meet a (neg b) = meet (neg b) a := by
    have hx := exchangeNested a (neg b) a
    dsimp only at hx
    rw [exchange b a, absorbNegLeft, absorbNegRight, inv] at hx
    exact hx
  have comm (a b : A) : meet a b = meet b a := by
    simpa only [inv] using commNeg a (neg b)
  have exchangeInside (a b c : A) :
      meet (neg (meet (neg (meet (neg a) b)) c)) (meet (neg a) c) =
        meet c (meet (neg a) b) := by
    rw [b2, absorbNeg]
  have doubleAbsorb (a b : A) : meet a (meet (neg b) a) = meet (neg b) a := by
    rw [← exchangeInside b a a, b1]
  have complementMeet (a b : A) : meet (neg (meet a b)) a = meet (neg b) a := by
    have h := exchange (meet (neg b) a) a
    rw [exchange b a, doubleAbsorb a b] at h
    exact h
  have overlap (a b c : A) :
      meet (meet a b) (meet b c) = meet (meet a b) c := by
    let t := meet a b
    calc
      meet t (meet b c) = meet (neg (meet (neg c) t)) (meet b t) :=
        (b2 c t b).symm
      _ = meet (neg (meet (neg c) t)) t := by rw [absorbLast b a]
      _ = meet t c := exchange c t
  have assoc (a b c : A) : meet (meet a b) c = meet a (meet b c) := by
    calc
      meet (meet a b) c = meet (meet a b) (meet b c) := (overlap a b c).symm
      _ = meet (meet b c) (meet b a) := by rw [comm (meet a b), comm a b]
      _ = meet (meet b c) a := by rw [comm b c, overlap c b a, comm c b]
      _ = meet a (meet b c) := comm _ _
  exact ⟨inv, idem, comm, assoc, complementMeet, absorbFirstNeg⟩

theorem complement_involution {A : Type} (meet : A → A → A) (neg : A → A)
    (b1 : ∀ x y, meet (neg (meet (neg x) y)) x = x)
    (b2 : ∀ x y z, meet (neg (meet (neg x) y)) (meet z y) = meet y (meet z x))
    (x : A) : neg (neg x) = x :=
  (meredithLaws meet neg b1 b2).involution x

end PalomarI3380
