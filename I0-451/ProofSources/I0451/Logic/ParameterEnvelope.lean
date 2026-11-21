module
public import I0451.Logic.ZFModel

/-! The parameter-definability construction used for Berkeley embeddings.
It is enough to start with a transitive set containing the parameter
and close it under finite power iteration. The new marker cannot occur
in that closure, by Foundation. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem stage_retains_seed {seed n : V} (transitive : IsTransitive seed) (hn : n ∈ (ω : V)) :
    seed ⊆ powerIteration.result ![seed] n := by
  apply naturalNumber_induction (fun k => seed ⊆ powerIteration.result ![seed] k) _ _ _ n hn
  · have stage := powerStage_defined seed
    definability
  · rw [powerIteration.result_zero]
    exact subset_refl _
  · intro k hk ih x hx
    rw [powerIteration.result_succ ![seed] hk]
    change x ∈ ℘ (powerIteration.result ![seed] k)
    rw [mem_power_iff]
    exact (stage_transitive transitive hk).transitive x (ih x hx)

private theorem singleton_mem_powerHull {seed x : V} (hx : x ∈ powerHull seed) :
    ({x} : V) ∈ powerHull seed := by
  obtain ⟨n, hn, atStage⟩ := (mem_powerHull_iff seed x).mp hx
  refine (mem_powerHull_iff seed _).mpr ⟨succ n, ω_succ_closed hn, ?_⟩
  rw [powerIteration.result_succ ![seed] hn]
  change ({x} : V) ∈ ℘ (powerIteration.result ![seed] n)
  rw [mem_power_iff]
  intro y hy
  have same : y = x := by simpa using hy
  exact same.symm ▸ atStage

private theorem fixed_kpair_mem_powerHull {seed b x : V} (transitive : IsTransitive seed)
    (hb : b ∈ seed) (hx : x ∈ powerHull seed) : ⟨b,x⟩ₖ ∈ powerHull seed := by
  obtain ⟨n, hn, atStage⟩ := (mem_powerHull_iff seed x).mp hx
  have before : b ∈ powerIteration.result ![seed] n := stage_retains_seed transitive hn b hb
  refine (mem_powerHull_iff seed _).mpr ⟨succ (succ n), ω_succ_closed (ω_succ_closed hn), ?_⟩
  rw [powerIteration.result_succ ![seed] (ω_succ_closed hn), powerIteration.result_succ ![seed] hn]
  change ⟨b,x⟩ₖ ∈ ℘ (℘ (powerIteration.result ![seed] n))
  rw [mem_power_iff]
  intro z hz
  have forms : z = ({b} : V) ∨ z = ({b,x} : V) := by simpa [kpair] using hz
  rw [mem_power_iff]
  rcases forms with rfl | rfl
  · intro y hy
    have same : y = b := by simpa using hy
    exact same.symm ▸ before
  · intro y hy
    rcases (show y = b ∨ y = x by simpa using hy) with rfl | rfl
    · exact before
    · exact atStage

def Uncontained (D a : V) : Prop :=
  a ∈ D ∧ ∀ y ∈ D, a ∉ y

/-- A parameter is named by an uncontained marker and the first
coordinate shared by its pairs. -/
def NamesParameter (D b : V) : Prop :=
  ∃ A, Uncontained D A ∧ ∃ p ∈ A, ∀ q ∈ p, b ∈ q

theorem parameterEnvelope (b : V) :
    ∃ D, IsTransitive D ∧ b ∈ D ∧ ∀ x ∈ D, NamesParameter D x ↔ x = b := by
  let seed := TransitiveClosure.transClosure ({b} : V)
  have transitive : IsTransitive seed := inferInstance
  have seedContains : b ∈ seed := TransitiveClosure.self_subset_transClosure b (by simp)
  let H := powerHull seed
  have hTrans : IsTransitive H := powerHull_transitive transitive
  have hContains : b ∈ H := (mem_powerHull_iff seed _).mpr
    ⟨0, zero_mem_ω, by rw [powerIteration.result_zero]; exact seedContains⟩
  let A := repl (fun x => ⟨b,x⟩ₖ) (by definability) H
  have members (p : V) : p ∈ A ↔ ∃ x ∈ H, p = ⟨b,x⟩ₖ := repl_spec _
  have covered : A ⊆ H := by
    intro w h
    obtain ⟨x, hx, rfl⟩ := (members w).mp h
    exact fixed_kpair_mem_powerHull transitive seedContains hx
  have new : A ∉ H := by
    intro inH
    have pairIn : ⟨b,A⟩ₖ ∈ A := (members _).mpr ⟨A, inH, rfl⟩
    have setIn : ({b,A} : V) ∈ ⟨b,A⟩ₖ := by simp [kpair]
    have markerIn : A ∈ ({b,A} : V) := by simp
    exact mem_asymm₃ markerIn setIn pairIn
  let D := insert A H
  have hD (x : V) : x ∈ D ↔ x = A ∨ x ∈ H := mem_insert
  have DTrans : IsTransitive D := by
    constructor
    intro x hx y hy
    rcases (hD x).mp hx with rfl | inside
    · exact (hD y).mpr (.inr (covered y hy))
    · exact (hD y).mpr (.inr (hTrans.transitive x inside y hy))
  have marker : Uncontained D A := by
    refine ⟨(hD A).mpr (.inl rfl), fun y hy membership => ?_⟩
    rcases (hD y).mp hy with rfl | inside
    · exact mem_irrefl A membership
    · exact new (hTrans.transitive y inside A membership)
  have onlyMarker (x : V) (named : Uncontained D x) : x = A := by
    rcases (hD x).mp named.1 with rfl | ordinary
    · rfl
    · have singleton := singleton_mem_powerHull ordinary
      exact False.elim (named.2 {x} ((hD _).mpr (.inr singleton)) (by simp))
  refine ⟨D, DTrans, (hD _).mpr (.inr hContains), fun x _ => ?_⟩
  constructor
  · rintro ⟨m, maximal, p, hp, name⟩
    rw [onlyMarker m maximal] at hp
    obtain ⟨y, _, rfl⟩ := (members p).mp hp
    have inSingleton : x ∈ ({b} : V) := name {b} (by simp [kpair])
    simpa using inSingleton
  · intro equal
    subst x
    refine ⟨A, marker, ⟨b,b⟩ₖ, (members _).mpr ⟨b, hContains, rfl⟩, ?_⟩
    intro q hq
    have which : q = ({b} : V) := by simpa [kpair] using hq
    simp [which]

def markerFormula : Identity.Formula 1 :=
  .ex (.conjunction
    (.universal (.negation (.mem 1 0)))
    (.ex (.conjunction (.mem 0 1) (.universal (.imp (.mem 0 1) (.mem 3 0))))))

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- On the transitive envelope, quantifiers bounded by a member of
the envelope range over every element of that member. -/
theorem markerFormula_eval {D : V} (transitive : IsTransitive D) (x : {x : V // x ∈ D}) :
    markerFormula.eval (fun a b : {x : V // x ∈ D} => a.val ∈ b.val) (fun _ => x) ↔
      NamesParameter D x.val := by
  simp only [markerFormula, Identity.Formula.eval, Identity.Formula.eval_conjunction,
    Identity.Formula.eval_universal, Identity.Formula.eval_negation]
  change (∃ A : {x : V // x ∈ D}, (∀ y : {x : V // x ∈ D}, A.val ∉ y.val) ∧
    ∃ p : {x : V // x ∈ D}, p.val ∈ A.val ∧
      ∀ q : {x : V // x ∈ D}, q.val ∈ p.val → x.val ∈ q.val) ↔ NamesParameter D x.val
  constructor
  · rintro ⟨A, maximal, p, hp, common⟩
    refine ⟨A.val, ⟨A.property, fun y hy => maximal ⟨y, hy⟩⟩, p.val, hp, ?_⟩
    intro q hq
    exact common ⟨q, transitive.transitive p.val p.property q hq⟩ hq
  · rintro ⟨A, maximal, p, hp, common⟩
    exact ⟨⟨A, maximal.1⟩, fun y => maximal.2 y.val y.property,
      ⟨p, transitive.transitive A maximal.1 p hp⟩, hp, fun q => common q.val⟩

theorem parameterEnvelope_fixes (b : V) :
    ∃ (D : V) (hb : b ∈ D), IsTransitive D ∧
      ∀ j : {x : V // x ∈ D} → {x : V // x ∈ D},
        (∀ {n : Nat} (f : Identity.Formula n) (args : Fin n → {x : V // x ∈ D}),
          f.eval (fun a b => a.val ∈ b.val) args ↔ f.eval (fun a b => a.val ∈ b.val) (j ∘ args)) →
        j ⟨b, hb⟩ = ⟨b, hb⟩ := by
  obtain ⟨D, transitive, hb, unique⟩ := parameterEnvelope b
  refine ⟨D, hb, transitive, fun j elementary => Subtype.ext ?_⟩
  let param : {x : V // x ∈ D} := ⟨b, hb⟩
  have marker := (markerFormula_eval transitive param).mpr ((unique b hb).mpr rfl)
  have preserved := (elementary markerFormula (fun _ => param)).mp marker
  have named := (markerFormula_eval transitive (j param)).mp preserved
  exact (unique _ (j param).property).mp named

end I0451.Logic.ZFModel
