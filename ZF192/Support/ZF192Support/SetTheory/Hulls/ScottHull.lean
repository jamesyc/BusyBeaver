module
public import ZF192Support.SetTheory.Hulls.ScottWitnesses
@[expose] public section
namespace FFL.FirstOrder.SetTheory.ScottHulls
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def hullStep (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed g : V) : V :=
 seed ∪ ⋃ˢ (repl (scottStep R hR) (scottStep_definable R hR) (range g))

theorem hullStep_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) :
 ℒₛₑₜ-function₁ (hullStep R hR seed) := by
 have hs := scottStep_definable R hR
 unfold hullStep; definability

noncomputable def hullStage (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed a : V) : V :=
 Replacement.transfiniteRec (hullStep R hR seed) (hullStep_definable R hR seed) a

theorem hullStage_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) :
 ℒₛₑₜ-function₁ (hullStage R hR seed) :=
 Replacement.transfiniteRec_definable (hullStep_definable R hR seed)

theorem hullStage_recursion (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) (a : Ordinal V) :
 hullStage R hR seed (a : V) = hullStep R hR seed
   (repl (fun b : V => ⟨b,hullStage R hR seed b⟩ₖ) (by have := hullStage_definable R hR seed; definability) (a : V)) :=
 Replacement.transfiniteRec_spec (hullStep R hR seed) (hullStep_definable R hR seed) a

theorem mem_hullStage_iff (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) (a : Ordinal V) (x : V) :
 x ∈ hullStage R hR seed (a : V) ↔
 x ∈ seed ∨ ∃ b ∈ (a : V), x ∈ scottStep R hR (hullStage R hR seed b) := by
 rw [hullStage_recursion]
 simp only [hullStep,mem_union_iff,mem_sUnion_iff,repl_spec,mem_range_iff,kpair_iff]
 constructor
 · rintro (hx | ⟨p,⟨y,⟨z,b,hb,hpair⟩,rfl⟩,hxp⟩)
   · exact Or.inl hx
   · exact Or.inr ⟨b,hb,by simpa only [hpair.2] using hxp⟩
 · rintro (hx | ⟨b,hb,hx⟩)
   · exact Or.inl hx
   · exact Or.inr ⟨scottStep R hR (hullStage R hR seed b),
       ⟨hullStage R hR seed b,⟨b,b,hb,rfl,rfl⟩,rfl⟩,hx⟩

theorem seed_subset_hullStage (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) (a : Ordinal V) :
 seed ⊆ hullStage R hR seed (a : V) := by
 intro x hx; exact (mem_hullStage_iff R hR seed a x).mpr (Or.inl hx)

theorem step_subset_hullStage (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V)
 (a : Ordinal V) {b : V} (hb : b ∈ (a : V)) :
 scottStep R hR (hullStage R hR seed b) ⊆ hullStage R hR seed (a : V) := by
 intro x hx; exact (mem_hullStage_iff R hR seed a x).mpr (Or.inr ⟨b,hb,hx⟩)

theorem hullStage_predecessors (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V)
 (hseed : ∀ x ∈ seed, ∃ u, R u x) (a : Ordinal V) :
 ∀ x ∈ hullStage R hR seed (a : V), ∃ u, R u x := by
 have hs := hullStage_definable R hR seed
 apply transfinite_induction (fun a : V => ∀ x ∈ hullStage R hR seed a, ∃ u, R u x) (by definability) _ a
 intro b ih x hx
 rcases (mem_hullStage_iff R hR seed b x).mp hx with hx | ⟨c,hcb,hx⟩
 · exact hseed x hx
 · let co : Ordinal V := ⟨c,IsOrdinal.of_mem hcb⟩
   exact scottStep_preserves_predecessors R hR (hullStage R hR seed c) (ih co hcb) x hx

noncomputable def scottHull (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V) : V :=
 hullStage R hR seed ω

theorem hull_member_in_natural_stage (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V)
 {x : V} (hx : x ∈ scottHull R hR seed) : ∃ n ∈ (ω : V), x ∈ hullStage R hR seed n := by
 rcases (mem_hullStage_iff R hR seed (Ordinal.ω) x).mp hx with hx | ⟨n,hn,hx⟩
 · exact ⟨∅,by simp,seed_subset_hullStage R hR seed ⟨∅,inferInstance⟩ x hx⟩
 · haveI : IsOrdinal n := IsOrdinal.nat hn
   exact ⟨succ n,ω_succ_closed hn,step_subset_hullStage R hR seed ⟨succ n,inferInstance⟩ (by simp) x hx⟩

theorem scottHull_closed (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V)
 {z u : V} (hz : z ∈ scottHull R hR seed) (hu : u ⊆ z) (hne : ∃ v, R u v) :
 ∃ v ∈ scottHull R hR seed, R u v := by
 obtain ⟨n,hn,hzn⟩ := hull_member_in_natural_stage R hR seed hz
 obtain ⟨v,hv,huv⟩ := scottStep_subset_fiber R hR hzn hu hne
 exact ⟨v,step_subset_hullStage R hR seed Ordinal.ω hn v hv,huv⟩

theorem scottHull_predecessors (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (seed : V)
 (hseed : ∀ x ∈ seed, ∃ u, R u x) : ∀ x ∈ scottHull R hR seed, ∃ u, R u x :=
 hullStage_predecessors R hR seed hseed Ordinal.ω

/-- The pointed hull required by the distinct-label gate, proved for every
first-order definable relation in an arbitrary ZF model. -/
theorem binary_pointed_hull (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (u₀ v₀ : V) :
 ∃ C : V, (R u₀ v₀ → v₀ ∈ C) ∧
   ∀ z ∈ C, (∃ p, R p z) ∧
     ∀ u, u ⊆ z → (∃ v, R u v) → ∃ w ∈ C, R u w := by
 let seed := sep ({v₀} : V) (R u₀) (by definability)
 have hseed : ∀ x ∈ seed, ∃ u, R u x := by
   intro x hx
   have hxR : R u₀ x := (mem_sep_iff.mp hx).2
   exact ⟨u₀,hxR⟩
 refine ⟨scottHull R hR seed,?_,?_⟩
 · intro h
   apply seed_subset_hullStage R hR seed Ordinal.ω v₀
   simp [seed,h]
 · intro z hz
   refine ⟨scottHull_predecessors R hR seed hseed z hz,?_⟩
   intro u hu he
   exact scottHull_closed R hR seed hz hu he

end FFL.FirstOrder.SetTheory.ScottHulls
