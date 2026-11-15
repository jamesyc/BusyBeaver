module
public import HierarchyProperties
@[expose] public section
namespace FFL.FirstOrder.SetTheory.ZF209Experiment
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def LeastFiberStage (R : V → V → Prop) (u a : V) : Prop :=
 IsOrdinal a ∧ (∃ v ∈ hierarchy a, R u v) ∧
 ∀ b : V, IsOrdinal b → (∃ v ∈ hierarchy b, R u v) → a ⊆ b

def ScottSpec (R : V → V → Prop) (u w : V) : Prop :=
 (¬(∃ v, R u v)) ∧ w = ∅ ∨
 ∃ a, LeastFiberStage R u a ∧ ∀ v, v ∈ w ↔ v ∈ hierarchy a ∧ R u v

theorem ScottSpec_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
 ℒₛₑₜ-relation (ScottSpec R) := by unfold ScottSpec LeastFiberStage; definability

theorem leastFiberStage_unique {R : V → V → Prop} {u a b : V}
 (ha : LeastFiberStage R u a) (hb : LeastFiberStage R u b) : a = b :=
 subset_antisymm (ha.2.2 b hb.1 hb.2.1) (hb.2.2 a ha.1 ha.2.1)

theorem scottSpec_existsUnique (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (u : V) :
 ∃! w, ScottSpec R u w := by
 classical
 by_cases he : ∃ v, R u v
 · obtain ⟨a,ha,hm⟩ := least_stage_for_definable_class (R u) (by definability) he
   have hla : LeastFiberStage R u a := ⟨a.ordinal,ha,fun b hb hv => hm ⟨b,hb⟩ hv⟩
   let w := sep (a |> Ordinal.val |> hierarchy) (R u) (by definability)
   have hw : ∀ v, v ∈ w ↔ v ∈ hierarchy (a : V) ∧ R u v := by intro v; simp [w]
   refine ⟨w,Or.inr ⟨a,hla,hw⟩,?_⟩
   intro z hz
   rcases hz with hz | ⟨b,hb,hzb⟩
   · exact False.elim (hz.1 he)
   · have hab : (a : V) = b := leastFiberStage_unique hla hb
     ext v
     rw [hzb,hw,hab]
 · refine ⟨∅,Or.inl ⟨he,rfl⟩,?_⟩
   intro w hw
   rcases hw with hw | ⟨a,ha,_⟩
   · exact hw.2
   · obtain ⟨v,_,hv⟩ := ha.2.1
     exact False.elim (he ⟨v,hv⟩)

/-- Unique, definable set of ALL fiber witnesses in the least meeting stage.
This chooses a uniquely characterized set, not a representative of the fiber. -/
noncomputable def scottSupport (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (u : V) : V :=
 Classical.choose! (scottSpec_existsUnique R hR u)

theorem scottSupport_spec (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (u : V) :
 ScottSpec R u (scottSupport R hR u) := Classical.choose!_spec (scottSpec_existsUnique R hR u)

theorem scottSupport_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
 ℒₛₑₜ-function₁ (scottSupport R hR) := by
 suffices ℒₛₑₜ-relation (fun w u => w = scottSupport R hR u) by exact this
 simp only [scottSupport,Classical.choose!_eq_iff_right]
 have hs := ScottSpec_definable R hR
 definability

theorem scottSupport_member {R : V → V → Prop} (hR : ℒₛₑₜ-relation R) {u v : V}
 (hv : v ∈ scottSupport R hR u) : R u v := by
 rcases scottSupport_spec R hR u with ⟨_,he⟩ | ⟨a,ha,hs⟩
 · simpa [he] using hv
 · exact ((hs v).mp hv).2

theorem scottSupport_nonempty_iff (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (u : V) :
 IsNonempty (scottSupport R hR u) ↔ ∃ v, R u v := by
 constructor
 · rintro ⟨v,hv⟩; exact ⟨v,scottSupport_member hR hv⟩
 · intro he
   rcases scottSupport_spec R hR u with ⟨hn,_⟩ | ⟨a,ha,hs⟩
   · exact False.elim (hn he)
   · obtain ⟨v,hva,hv⟩ := ha.2.1
     exact ⟨v,(hs v).mpr ⟨hva,hv⟩⟩

/-- Internal union of the definable support sets over a specified domain. -/
noncomputable def scottImage (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (X : V) : V :=
 ⋃ˢ (repl (scottSupport R hR) (scottSupport_definable R hR) X)

theorem scottImage_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
 ℒₛₑₜ-function₁ (scottImage R hR) := by
 have hs := scottSupport_definable R hR
 unfold scottImage
 definability

theorem mem_scottImage_iff (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (X v : V) :
 v ∈ scottImage R hR X ↔ ∃ u ∈ X, v ∈ scottSupport R hR u := by
 simp only [scottImage,mem_sUnion_iff,repl_spec]
 constructor
 · rintro ⟨w,⟨u,hu,rfl⟩,hv⟩; exact ⟨u,hu,hv⟩
 · rintro ⟨u,hu,hv⟩; exact ⟨scottSupport R hR u,⟨u,hu,rfl⟩,hv⟩

theorem scottImage_members_have_predecessor (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
 (X : V) {v : V} (hv : v ∈ scottImage R hR X) : ∃ u ∈ X, R u v := by
 obtain ⟨u,hu,hv⟩ := (mem_scottImage_iff R hR X v).mp hv
 exact ⟨u,hu,scottSupport_member hR hv⟩

theorem scottImage_meets_fiber (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
 {X u : V} (hu : u ∈ X) (hne : ∃ v, R u v) : ∃ v ∈ scottImage R hR X, R u v := by
 obtain ⟨v,hv⟩ := (scottSupport_nonempty_iff R hR u).mpr hne
 exact ⟨v,(mem_scottImage_iff R hR X v).mpr ⟨u,hu,hv⟩,scottSupport_member hR hv⟩

noncomputable def subsetDomain (D : V) : V := ⋃ˢ (repl power (by definability) D)

instance subsetDomain_definable : ℒₛₑₜ-function₁ (subsetDomain : V → V) := by
 unfold subsetDomain; definability

theorem mem_subsetDomain_iff (D u : V) : u ∈ subsetDomain D ↔ ∃ z ∈ D, u ⊆ z := by
 simp only [subsetDomain,mem_sUnion_iff,repl_spec]
 constructor
 · rintro ⟨p,⟨z,hz,rfl⟩,hp⟩; exact ⟨z,hz,mem_power_iff.mp hp⟩
 · rintro ⟨z,hz,hu⟩; exact ⟨power z,⟨z,hz,rfl⟩,mem_power_iff.mpr hu⟩

noncomputable def scottStep (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (D : V) : V :=
 D ∪ scottImage R hR (subsetDomain D)

theorem scottStep_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
 ℒₛₑₜ-function₁ (scottStep R hR) := by
 have hs := scottImage_definable R hR
 unfold scottStep; definability

theorem scottStep_preserves_predecessors (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
 (D : V) (hD : ∀ v ∈ D, ∃ u, R u v) : ∀ v ∈ scottStep R hR D, ∃ u, R u v := by
 intro v hv
 rcases mem_union_iff.mp hv with hv | hv
 · exact hD v hv
 · obtain ⟨u,_,huv⟩ := scottImage_members_have_predecessor R hR (subsetDomain D) hv
   exact ⟨u,huv⟩

theorem scottStep_subset_fiber (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
 {D z u : V} (hz : z ∈ D) (hu : u ⊆ z) (hne : ∃ v, R u v) :
 ∃ v ∈ scottStep R hR D, R u v := by
 have huD : u ∈ subsetDomain D := (mem_subsetDomain_iff D u).mpr ⟨z,hz,hu⟩
 obtain ⟨v,hv,huv⟩ := scottImage_meets_fiber R hR huD hne
 exact ⟨v,mem_union_iff.mpr (Or.inr hv),huv⟩

end FFL.FirstOrder.SetTheory.ZF209Experiment
