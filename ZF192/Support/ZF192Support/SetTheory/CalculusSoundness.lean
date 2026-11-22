module
public import ZF192Support.Calculus.Standard.History
public import ZF192Support.SetTheory.GateValidity

@[expose] public section
/-! # Soundness of standard C derivations in ZF models -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory CCodeSoundness

private theorem exact_axiom_true {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {n : Nat} (hn : ExactAxiom n) (s : ℕ → V) :
    evalCode (fun a b : V => a ∈ b) n s := by
  let E := fun a b : V => a ∈ b
  have hirr : ∀ x, ¬ E x x := fun x => mem_irrefl x
  rcases hn with rfl | ⟨a, d, h, u, hn⟩
  · exact (evalCode_of_formula .truth E s).mpr trivial
  · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨had, hah, rfl⟩
    · exact eval_head1 E a d h s
    · exact eval_head2 E hirr a d h s
    · exact eval_head3 E a d h s
    · exact eval_head4 E a d h s
    · exact eval_head5 E a d h s
    · exact eval_head6 E hirr a d h s
    · exact eval_rho8 E a d h u s
    · exact ZFR.FoundationBridge.pointedGate_valid a d h had hah s

/-- Theorems of the machine's calculus hold in every model of ZF. -/
theorem exact_true {x : ℕ} (hx : ExactProvable x) {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (s : ℕ → V) : evalCode (fun a b : V => a ∈ b) x s := by
  obtain ⟨xs, hxs, hm⟩ := hx
  induction hxs generalizing x s with
  | nil => simp at hm
  | axRule n _ _ hn ih =>
    rcases List.mem_cons.mp hm with he | ht
    · subst x
      exact exact_axiom_true hn s
    · exact ih s ht
  | mp b c _ _ hb hi ih =>
    rcases List.mem_cons.mp hm with he | ht
    · subst x
      exact (evalCode_imp _ b c s).mp (ih s hi) (ih s hb)
    · exact ih s ht
  | gen i b _ _ hb ih =>
    rcases List.mem_cons.mp hm with he | ht
    · subst x
      exact (evalCode_all _ i b s).mpr fun v => ih (update s i v) hb
    · exact ih s ht

end ZF192Support.Halting
