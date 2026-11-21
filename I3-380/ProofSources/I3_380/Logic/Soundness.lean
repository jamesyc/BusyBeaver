module
public import I3_380.Logic.I3
@[expose] public section

namespace PalomarI3380.Logic.NDSemantics

universe u

theorem eval_rename {V : Type u} (E : V → V → Prop) (p : Formula)
    (σ : Nat → Nat) (s : Nat → V) :
    eval E (rename σ p) s ↔ eval E p (s ∘ σ) := by
  have binder (σ : Nat → Nat) (s : Nat → V) (x : V) :
      pushValue s x ∘ lift σ = pushValue (s ∘ σ) x := by
    funext n
    cases n <;> rfl
  induction p generalizing σ s <;>
    simp only [rename, eval, Function.comp_apply, *]

variable {V : Type u} (mem : V → V → Prop)
def ContextTrue (Γ : Context) (s : Nat → V) := ∀ p ∈ Γ, eval mem p s
def RowTrue : Row → Prop
 | .seq Γ p => ∀ s, ContextTrue mem Γ s → eval mem p s
 | .branches Γ a b c => ∀ s, ContextTrue mem Γ s →
     (eval mem a s → eval mem c s) ∧ (eval mem b s → eval mem c s)
theorem shift_eval (p : Formula) (s : Nat → V) (x : V) :
 eval mem (shift p) (pushValue s x) ↔ eval mem p s := by
 exact eval_rename mem p Nat.succ (pushValue s x)
theorem subst_eval (p : Formula) (s : Nat → V) (t : Nat) :
 eval mem (subst t p) s ↔ eval mem p (pushValue s (s t)) := by
 have he : s ∘ substMap t = pushValue s (s t) := by
  funext i; cases i <;> rfl
 simpa only [subst,he] using eval_rename mem p (substMap t) s
theorem context_cons {Γ : Context} {s : Nat → V} {p : Formula}
 (hp : eval mem p s) (hΓ : ContextTrue mem Γ s) : ContextTrue mem (p::Γ) s := by
 intro q hq; rcases List.mem_cons.mp hq with rfl | hq
 · exact hp
 · exact hΓ q hq
theorem context_shift {Γ : Context} {s : Nat → V}
 (hΓ : ContextTrue mem Γ s) (x : V) : ContextTrue mem (shiftContext Γ) (pushValue s x) := by
 intro q hq
 obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
 exact (shift_eval mem p s x).mpr (hΓ p hp)
/-- Soundness of every source natural-deduction rule in an arbitrary relation
structure; no model existence or set-theory axiom is assumed. -/
theorem sound {r : Row} (h : ND r) : RowTrue mem r := by
 induction h with
 | ctx hm => exact fun s hΓ => hΓ _ hm
 | pc Γ a b =>
   intro s hΓ h
   by_cases ha : eval mem a s
   · exact ha
   · exact h (fun hp => False.elim (ha hp))
 | ii h ih => exact fun s hΓ ha => ih s (context_cons mem ha hΓ)
 | ie h1 h2 ih1 ih2 => exact fun s hΓ => ih1 s hΓ (ih2 s hΓ)
 | «exp» h ih => exact fun s hΓ => False.elim (ih s hΓ)
 | ci h1 h2 ih1 ih2 => exact fun s hΓ => ⟨ih1 s hΓ,ih2 s hΓ⟩
 | ce1 h ih => exact fun s hΓ => (ih s hΓ).1
 | ce2 h ih => exact fun s hΓ => (ih s hΓ).2
 | di1 h ih => exact fun s hΓ => Or.inl (ih s hΓ)
 | di2 h ih => exact fun s hΓ => Or.inr (ih s hΓ)
 | branchPair h1 h2 ih1 ih2 =>
   exact fun s hΓ => ⟨fun ha => ih1 s (context_cons mem ha hΓ),fun hb => ih2 s (context_cons mem hb hΓ)⟩
 | de h1 h2 ih1 ih2 => exact fun s hΓ => (ih1 s hΓ).elim (ih2 s hΓ).1 (ih2 s hΓ).2
 | wk hs h ih => exact fun s hΔ => ih s (fun p hp => hΔ p (hs p hp))
 | allI h ih => exact fun s hΓ x => ih (pushValue s x) (context_shift mem hΓ x)
 | allE t h ih => exact fun s hΓ => (subst_eval mem _ s t).mpr (ih s hΓ (s t))
 | exI t h ih => exact fun s hΓ => ⟨s t,(subst_eval mem _ s t).mp (ih s hΓ)⟩
 | exE h1 h2 ih1 ih2 =>
   intro s hΓ
   obtain ⟨x,hx⟩ := ih1 s hΓ
   exact (shift_eval mem _ s x).mp (ih2 (pushValue s x) (context_cons mem hx (context_shift mem hΓ x)))

theorem consistency_of_model {V : Type} (E : V → V → Prop) (inhabited : Nonempty V)
    (model : ZFCI3Model E) : ZFCI3Consistent := by
  intro refutation
  obtain ⟨context, axioms, proof⟩ := refutation
  obtain ⟨point⟩ := inhabited
  exact (sound E proof) (fun _ => point) (fun p hp => model p (axioms p hp) _)

end PalomarI3380.Logic.NDSemantics
