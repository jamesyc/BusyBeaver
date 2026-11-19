module
public import PairingBridge
@[expose] public section
namespace C207Search
open C207Soundness

theorem history_append {xs : List Nat} (hx : ExactHistory xs) (ys : List Nat)
    (hy : ExactHistory ys) : ExactHistory (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | axRule n xs hx ha ih => exact .axRule n _ ih ha
  | mp b c xs hx hb hi ih =>
    exact .mp b c _ ih (List.mem_append_left _ hb) (List.mem_append_left _ hi)
  | gen i b xs hx hb ih => exact .gen i b _ ih (List.mem_append_left _ hb)

theorem proved_axiom {n : Nat} (h : ExactAxiom n) : ExactProvable n :=
  ⟨[n], .axRule n [] .nil h, by simp⟩

theorem proved_zero : ExactProvable 0 := proved_axiom (Or.inl rfl)

theorem proved_mp {a b : Nat} (ha : ExactProvable a) (hi : ExactProvable (impCode a b)) :
    ExactProvable b := by
  obtain ⟨xs,hx,hax⟩ := ha
  obtain ⟨ys,hy,hiy⟩ := hi
  exact ⟨b :: (xs ++ ys), .mp a b _ (history_append hx ys hy)
    (List.mem_append_left _ hax) (List.mem_append_right _ hiy), by simp⟩

theorem proved_gen (i : Nat) {a : Nat} (ha : ExactProvable a) : ExactProvable (allCode i a) := by
  obtain ⟨xs,hx,ha⟩ := ha
  exact ⟨allCode i a :: xs,.gen i a xs hx ha,by simp⟩

inductive Derivable : Nat → Prop
  | ax {n : Nat} : ExactAxiom n → Derivable n
  | mp {a b : Nat} : Derivable a → Derivable (impCode a b) → Derivable b
  | gen (i : Nat) {a : Nat} : Derivable a → Derivable (allCode i a)

theorem derivable_iff_provable (n : Nat) : Derivable n ↔ ExactProvable n := by
  constructor
  · intro h
    induction h with
    | ax h => exact proved_axiom h
    | mp _ _ ih1 ih2 => exact proved_mp ih1 ih2
    | gen i _ ih => exact proved_gen i ih
  · rintro ⟨xs,hx,hn⟩
    have hs : ∀ n ∈ xs, Derivable n := by
      clear hn
      induction hx with
      | nil => simp
      | axRule a xs hx ha ih =>
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact .ax ha
        · exact ih n hn
      | mp a b xs hx ha hi ih =>
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact .mp (ih a ha) (ih _ hi)
        · exact ih n hn
      | gen i a xs hx ha ih =>
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact .gen i (ih a ha)
        · exact ih n hn
    exact hs n hn
end C207Search
