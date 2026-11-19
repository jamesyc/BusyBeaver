module
public import ZfrCoreEndpoints
public import ExactHistorySoundness
@[expose] public section
namespace ZFR
open C207Soundness

/-- Source proof with an explicit finite context of actual ZFR axioms. -/
def SourceTheorem (p : Formula) : Prop :=
 ∃ Γ : Context, (∀ a, a ∈ Γ → sourceZfrAxiom (encodeFormula a)) ∧ ND (.seq Γ p)

theorem SourceTheorem.numeric {p : Formula} (h : SourceTheorem p) : ZfrProvable (encodeFormula p) := by
 obtain ⟨Γ,hΓ,h⟩ := h
 exact h.theoryProvable hΓ

theorem SourceTheorem.of_core {p : Formula} (h : ND (.seq coreContext p)) : SourceTheorem p :=
 ⟨coreContext,coreContext_in_zfr,h⟩

theorem SourceTheorem.mp {p q : Formula} (hp : SourceTheorem p) (hi : SourceTheorem (.imp p q)) :
 SourceTheorem q := by
 obtain ⟨Γ,hΓ,hp⟩ := hp
 obtain ⟨Δ,hΔ,hi⟩ := hi
 refine ⟨Γ++Δ,?_,ND.ie (ND.wk (fun a ha => List.mem_append_right Γ ha) hi)
   (ND.wk (fun a ha => List.mem_append_left Δ ha) hp)⟩
 intro a ha
 rcases List.mem_append.mp ha with h | h
 · exact hΓ a h
 · exact hΔ a h

theorem SourceTheorem.code_mp (a b : Nat)
 (ha : SourceTheorem (translateCode id a))
 (hi : SourceTheorem (translateCode id (impCode a b))) : SourceTheorem (translateCode id b) := by
 obtain ⟨Γ,hΓ,ha⟩ := ha
 obtain ⟨Δ,hΔ,hi⟩ := hi
 refine ⟨Γ++Δ,?_,nd_mp_code a b
   (ND.wk (fun a ha => List.mem_append_left Δ ha) ha)
   (ND.wk (fun a ha => List.mem_append_right Γ ha) hi)⟩
 intro a ha
 rcases List.mem_append.mp ha with h | h
 · exact hΓ a h
 · exact hΔ a h

theorem SourceTheorem.code_gen (i a : Nat) (ha : SourceTheorem (translateCode id a)) :
 SourceTheorem (translateCode id (allCode i a)) := by
 obtain ⟨Γ,hΓ,ha⟩ := ha
 have hc : ClosedContext Γ := by
  intro p hp
  exact (sourceBound_encode p 0).mp (sourceZfrAxiom_closed (hΓ p hp))
 exact ⟨Γ,hΓ,nd_generalize_code hc i a ha⟩

/-- The ONLY outstanding axiom family in the syntactic reverse translation.
This is an explicit open obligation, not an axiom declaration or a proof. -/
def GateTranslationObligation : Prop := ∀ a d h, a ≠ d → a ≠ h →
 SourceTheorem (translateCode id (pointedGateCode a d h))

theorem exact_axiom_translation (gate : GateTranslationObligation) (n : Nat) (hn : ExactAxiom n) :
 SourceTheorem (translateCode id n) := by
 rcases hn with rfl | ⟨a,d,h,u,hn⟩
 · rw [translateCode_zero]; exact SourceTheorem.of_core (nd_truth _)
 · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨had,hah,rfl⟩
   · exact SourceTheorem.of_core (core_head1 a d h)
   · exact SourceTheorem.of_core (core_head2 a d h)
   · exact SourceTheorem.of_core (core_head3 a d h)
   · exact SourceTheorem.of_core (core_head4 a d h)
   · exact SourceTheorem.of_core (core_head5 a d h)
   · exact SourceTheorem.of_core (core_head6 a d h)
   · exact SourceTheorem.of_core (core_rho8 a d h u)
   · exact gate a d h had hah

theorem exact_history_translation (gate : GateTranslationObligation)
 {xs : List Nat} (hx : ExactHistory xs) : ∀ n, n ∈ xs → SourceTheorem (translateCode id n) := by
 induction hx with
 | nil => simp
 | axRule n xs hx hn ih =>
   intro c hc
   rcases List.mem_cons.mp hc with he | hc
   · subst c
     exact exact_axiom_translation gate n hn
   · exact ih c hc
 | mp b c xs hx hb hi ih =>
   intro n hn
   rcases List.mem_cons.mp hn with he | hn
   · subst n
     exact SourceTheorem.code_mp b c (ih b hb) (ih (impCode b c) hi)
   · exact ih n hn
 | gen i b xs hx hb ih =>
   intro n hn
   rcases List.mem_cons.mp hn with he | hn
   · subst n
     exact SourceTheorem.code_gen i b (ih b hb)
   · exact ih n hn

/-- Conditional only on the named, still-unproved syntactic gate obligation. -/
theorem reverse_calibration_pending_gate (gate : GateTranslationObligation)
 (h : ExactProvable 1) : ZfrProvable 0 := by
 obtain ⟨xs,hx,hm⟩ := h
 have ht := exact_history_translation gate hx 1 hm
 rw [translateCode_one] at ht
 exact (ht.mp (SourceTheorem.of_core (core_irreflexivity 0))).numeric

end ZFR
