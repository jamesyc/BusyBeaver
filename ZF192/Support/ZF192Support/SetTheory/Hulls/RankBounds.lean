module
public import ZF192Support.SetTheory.Hulls.RankStages
public import Foundation.FirstOrder.SetTheory.TransitiveClosure
@[expose] public section
namespace FFL.FirstOrder.SetTheory.ScottHulls
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_hierarchy_iff (a : Ordinal V) (x : V) :
 x ∈ hierarchy (a : V) ↔ ∃ b ∈ (a : V), x ⊆ hierarchy b := by
 rw [hierarchy_recursion]
 simp only [stageStep,mem_sUnion_iff,repl_spec,mem_range_iff,kpair_iff]
 constructor
 · rintro ⟨p,⟨y,⟨z,b,hb,hpair⟩,rfl⟩,hxp⟩
   exact ⟨b,hb,by simpa only [hpair.2] using mem_power_iff.mp hxp⟩
 · rintro ⟨b,hb,hx⟩
   exact ⟨power (hierarchy b),⟨hierarchy b,⟨b,b,hb,rfl,rfl⟩,rfl⟩,mem_power_iff.mpr hx⟩

theorem hierarchy_mono (a b : Ordinal V) (hab : (a : V) ⊆ (b : V)) :
 hierarchy (a : V) ⊆ hierarchy (b : V) := by
 intro x hx
 obtain ⟨c,hc,hx⟩ := (mem_hierarchy_iff a x).mp hx
 exact (mem_hierarchy_iff b x).mpr ⟨c,hab c hc,hx⟩

theorem hierarchy_successor (a : Ordinal V) :
 hierarchy (succ (a : V)) = power (hierarchy (a : V)) := by
 ext x
 rw [mem_hierarchy_iff (⟨succ (a : V),inferInstance⟩ : Ordinal V),mem_power_iff]
 constructor
 · rintro ⟨b,hb,hx⟩
   rcases mem_succ_iff.mp hb with he | hba
   · simpa only [he] using hx
   · let bOrd : Ordinal V := ⟨b,IsOrdinal.of_mem hba⟩
     exact subset_trans hx (hierarchy_mono bOrd a (a.ordinal.transitive b hba))
 · intro hx
   exact ⟨a,by simp,hx⟩

/-- Definable membership induction, proved via a set-sized counterexample
subset of TC({x}); no external well-foundedness of a model is assumed. -/
theorem definable_membership_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
 (step : ∀ x, (∀ y ∈ x, P y) → P x) (x : V) : P x := by
 classical
 let A := TransitiveClosure.transClosure ({x} : V)
 have hA : IsTransitive A := inferInstance
 have hxA : x ∈ A := TransitiveClosure.self_subset_transClosure x (by simp)
 by_contra hx
 let B := sep A (fun y => ¬P y) (by definability)
 have hxB : x ∈ B := by simp [B,hxA,hx]
 have : IsNonempty B := ⟨x,hxB⟩
 obtain ⟨z,hzB,hmin⟩ := foundation B
 have hz : z ∈ A ∧ ¬P z := by simpa [B] using hzB
 apply hz.2
 apply step z
 intro y hyz
 by_contra hy
 have hyA := hA.transitive z hz.1 y hyz
 have hyB : y ∈ B := by simp [B,hyA,hy]
 exact hmin y hyB hyz

def Covered (x : V) : Prop := ∃ a : V, IsOrdinal a ∧ x ∈ hierarchy a

instance Covered_definable : ℒₛₑₜ-predicate (Covered : V → Prop) := by
 unfold Covered; definability

def LeastLevel (x a : V) : Prop := IsOrdinal a ∧ x ∈ hierarchy a ∧
 ∀ b : V, IsOrdinal b → x ∈ hierarchy b → a ⊆ b

instance LeastLevel_definable : ℒₛₑₜ-relation (LeastLevel : V → V → Prop) := by
 unfold LeastLevel; definability

theorem leastLevel_existsUnique {x : V} (hx : Covered x) : ∃! a, LeastLevel x a := by
 obtain ⟨a,ha,hxa⟩ := hx
 have he : ∃ a : Ordinal V, x ∈ hierarchy (a : V) := ⟨⟨a,ha⟩,hxa⟩
 obtain ⟨b,hb,hleast⟩ := exists_minimal (fun a : V => x ∈ hierarchy a) (by definability) he
 refine ⟨b,⟨b.ordinal,hb,?_⟩,?_⟩
 · intro c hc hxc
   exact hleast ⟨c,hc⟩ hxc
 · intro c hc
   exact subset_antisymm (hc.2.2 b b.ordinal hb) (hleast ⟨c,hc.1⟩ hc.2.1)

theorem covered_of_members (x : V) (hx : ∀ y ∈ x, Covered y) : Covered x := by
 obtain ⟨Y,hY⟩ := replacement_rel_exists_of_mem_existsUnique x LeastLevel
   (fun y hy => leastLevel_existsUnique (hx y hy)) (by definability)
 have hYo : ∀ a ∈ Y, IsOrdinal a := by
   intro a ha
   obtain ⟨y,hy,hya⟩ := (hY a).mp ha
   exact hya.1
 let a : Ordinal V := ⟨⋃ˢ Y,IsOrdinal.sUnion hYo⟩
 have hxa : x ⊆ hierarchy (a : V) := by
   intro y hy
   obtain ⟨b,hb,_⟩ := leastLevel_existsUnique (hx y hy)
   have hbY : b ∈ Y := (hY b).mpr ⟨y,hy,hb⟩
   exact hierarchy_mono ⟨b,hb.1⟩ a (subset_sUnion_of_mem hbY) y hb.2.1
 haveI : IsOrdinal (a : V) := a.ordinal
 refine ⟨succ (a : V),inferInstance,?_⟩
 rw [hierarchy_successor]
 exact mem_power_iff.mpr hxa

theorem hierarchy_covers (x : V) : ∃ a : Ordinal V, x ∈ hierarchy (a : V) := by
 have hx : Covered x := definable_membership_induction Covered (by definability) covered_of_members x
 obtain ⟨a,ha,hx⟩ := hx
 exact ⟨⟨a,ha⟩,hx⟩

/-- A definable nonempty class of sets meets a least hierarchy stage.
The witnesses are bounded internally; this does not choose a set from the class. -/
theorem least_stage_for_definable_class (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
 (hne : ∃ x, P x) : ∃ a : Ordinal V,
 (∃ x ∈ hierarchy (a : V), P x) ∧
 ∀ b : Ordinal V, (∃ x ∈ hierarchy (b : V), P x) → (a : V) ⊆ (b : V) := by
 obtain ⟨x,hx⟩ := hne
 obtain ⟨a,hxa⟩ := hierarchy_covers x
 exact exists_minimal (fun b : V => ∃ x ∈ hierarchy b, P x) (by definability) ⟨a,x,hxa,hx⟩

end FFL.FirstOrder.SetTheory.ScottHulls
