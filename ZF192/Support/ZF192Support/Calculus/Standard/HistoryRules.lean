module
public import ZF192Support.Calculus.Standard.History
@[expose] public section
namespace CProofSearch
open CCodeSoundness

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

end CProofSearch
