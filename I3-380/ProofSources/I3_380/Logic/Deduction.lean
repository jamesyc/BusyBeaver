module
public import I3_380.Logic.Renaming
@[expose] public section

namespace PalomarI3380.Logic

abbrev Theory := Formula → Prop

namespace Theory

def Derives (T : Theory) (p : Formula) : Prop :=
  ∃ Γ : Context, (∀ q ∈ Γ, T q) ∧ ND (.seq Γ p)

def Consistent (T : Theory) : Prop := ¬T.Derives .bot

def add (T : Theory) (p : Formula) : Theory := fun q => q = p ∨ T q

variable {T U : Theory} {p q r : Formula}

theorem Derives.of_axiom (h : T p) : T.Derives p :=
  ⟨[p],fun _ hq => (List.mem_singleton.mp hq).symm ▸ h,ND.ctx (by simp)⟩

theorem Derives.mono (h : T.Derives p) (inclusion : ∀ q, T q → U q) : U.Derives p := by
  obtain ⟨Γ,valid,proof⟩ := h
  exact ⟨Γ,fun q hq => inclusion q (valid q hq),proof⟩

theorem Derives.close_pair (first : T.Derives p) (second : T.Derives q)
    (rule : ∀ Γ, ND (.seq Γ p) → ND (.seq Γ q) → ND (.seq Γ r)) : T.Derives r := by
  obtain ⟨Γ,axioms,pr⟩ := first
  obtain ⟨Δ,axioms',qr⟩ := second
  refine ⟨Γ ++ Δ,fun s h => (List.mem_append.mp h).elim (axioms s) (axioms' s),?_⟩
  exact rule _ (ND.wk (fun _ h => List.mem_append_left _ h) pr)
    (ND.wk (fun _ h => List.mem_append_right _ h) qr)

theorem Derives.app (fn : T.Derives (.imp p q)) (arg : T.Derives p) : T.Derives q :=
  fn.close_pair arg fun _ => ND.ie

theorem Derives.conj (hp : T.Derives p) (hq : T.Derives q) : T.Derives (.and p q) :=
  hp.close_pair hq fun _ => ND.ci

theorem Derives.explode (h : T.Derives .bot) : T.Derives p := by
  obtain ⟨Γ,support,h⟩ := h
  exact ⟨Γ,support,ND.exp h⟩

theorem Derives.allE (h : T.Derives (.all p)) (i : Nat) : T.Derives (subst i p) := by
  obtain ⟨Γ,support,h⟩ := h
  exact ⟨Γ,support,ND.allE i h⟩

theorem Derives.exI (i : Nat) (h : T.Derives (subst i p)) : T.Derives (.ex p) := by
  obtain ⟨Γ,support,h⟩ := h
  exact ⟨Γ,support,ND.exI i h⟩

theorem Derives.map (h : T.Derives p) (rule : ∀ Γ, ND (.seq Γ p) → ND (.seq Γ q)) :
    T.Derives q := by
  obtain ⟨Γ,good,h⟩ := h
  exact ⟨Γ,good,rule Γ h⟩

theorem Derives.neg_elim (h : T.Derives (Neg (Neg p))) : T.Derives p := by
  apply h.map
  intro Γ proof
  apply ND.ie (ND.pc Γ p .bot)
  apply ND.ii
  exact ND.exp (ND.ie (ND.wk (fun _ => List.mem_cons_of_mem _) proof) (ND.ctx (List.mem_cons_self)))

theorem discharge (h : (T.add p).Derives q) : T.Derives (.imp p q) := by
  classical
  obtain ⟨Γ,support,h⟩ := h
  let Δ := Γ.filter (fun a => decide (T a))
  have raw : ∀ a ∈ Δ, T a := by simp [Δ]
  refine ⟨Δ,raw,ND.ii (ND.wk (fun a ha => ?_) h)⟩
  rcases support a ha with eq | base
  · exact List.mem_cons.mpr (Or.inl eq)
  · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨ha,decide_eq_true base⟩)

theorem consistent_add_iff (_h : T.Consistent) : (T.add p).Consistent ↔ ¬T.Derives (Neg p) := by
  constructor
  · intro extended denied
    exact extended ((denied.mono (fun _ => Or.inr)).app (.of_axiom (Or.inl rfl)))
  · intro notDenied refutes
    exact notDenied (discharge refutes)

theorem either_extension (h : T.Consistent) (p : Formula) :
    (T.add p).Consistent ∨ (T.add (Neg p)).Consistent := by
  classical
  by_cases first : (T.add p).Consistent
  · exact Or.inl first
  · refine Or.inr ((consistent_add_iff h).mpr fun notNot => ?_)
    have denied := Classical.byContradiction (fun notDenied => first ((consistent_add_iff h).mpr notDenied))
    exact h (denied.app notNot.neg_elim)

theorem add_bounded {a : Formula} {n : Nat} (h : ∀ p, T p → Bound p n) (ha : Bound a n) :
    ∀ p, (T.add a) p → Bound p n  :=
  fun p hp => hp.elim (fun eq => eq.symm ▸ ha) (h p)

theorem fresh_to_head {a : Formula} {n : Nat} (h : Bound a (n+1)) :
    rename (fun i => if i = n then 0 else i + 1) (subst n a) = a := by
  rw [subst,rename_comp]
  apply Eq.trans _ (rename_identity a)
  apply rename_agree a h
  intro i hi
  cases i with
  | zero => simp [Function.comp_apply,substMap]
  | succ i => simp [Function.comp_apply,substMap,show i ≠ n by omega]

/-- A witness at a fresh index can be added to a consistent theory when
that theory derives its existential closure. -/
theorem witness_consistent {a : Formula} {n : Nat} (h : T.Consistent)
    (bounded : ∀ p, T p → Bound p n) (ha : Bound a (n+1)) (some : T.Derives (.ex a)) :
    (T.add (subst n a)).Consistent := by
  rintro ⟨Γ,valid,refutes⟩
  classical
  let f : Nat → Nat := fun i => if i = n then 0 else i + 1
  let Γ₀ := Γ.filter (fun p => decide (T p))
  have isBase : ∀ p ∈ Γ₀, T p := by simp [Γ₀]
  obtain ⟨Δ,inTheory,someProof⟩ := some
  let C := Δ ++ Γ₀
  have related : ContextSub (Γ.map (rename f)) (a :: shiftContext C) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    rcases valid p hp with rfl | original
    · exact List.mem_cons.mpr (Or.inl (fresh_to_head ha))
    · have compatible : rename f p = shift p := by
        apply rename_agree p (bounded p original)
        intro i hi
        exact ite_eq_right (by omega)
      rw [compatible]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,List.mem_append_right _
        (List.mem_filter.mpr ⟨hp,decide_eq_true original⟩),rfl⟩)
  have after := ND.wk related (refutes.rename f)
  have finish : ND (.seq C .bot) :=
    ND.exE (ND.wk (fun _ hp => List.mem_append_left _ hp) someProof) after
  exact h ⟨C,fun p hp => (List.mem_append.mp hp).elim (inTheory p) (isBase p),finish⟩

end Theory
end PalomarI3380.Logic
