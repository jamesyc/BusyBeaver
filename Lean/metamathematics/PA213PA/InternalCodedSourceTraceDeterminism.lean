module

public import PA215PA.Theory
public import PA213PA.InternalCodedSourceTraceCompose

@[expose] public section
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] stepValue stepGraph traceGraph

def comparisonFormula : ArithmeticSemisentence 1 :=
  “i. ∀ n m cs ds a b c, !traceGraph n cs a b ∧ !traceGraph m ds a c →
    i≤n → i≤m → ∃ x, !nthDef x cs i ∧ !nthDef x ds i”
def stabilityFormula : ArithmeticSemisentence 1 :=
  “i. ∀ n cs a b, !traceGraph n cs a b ∧ !stepGraph a a →
    i≤n → !nthDef a cs i”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma comparison_correct (i : V) : (V ⊧/![i] comparisonFormula) ↔
    ∀ n m cs ds a b c : V, Trace n cs a b → Trace m ds a c →
      i≤n → i≤m → cs.[i]=ds.[i] := by
  simp [comparisonFormula,trace_correct,nth_defined.df]

lemma stability_correct (i : V) : (V ⊧/![i] stabilityFormula) ↔
    ∀ n cs a b : V, Trace n cs a b → stepValue a=a → i≤n → cs.[i]=a := by
  simp [stabilityFormula,trace_correct,step_defined.df,nth_defined.df,eq_comm]

theorem trace_agrees_at {n m cs ds a b c : V} (h : Trace n cs a b) (g : Trace m ds a c)
    (i : V) (hi : i≤n) (hj : i≤m) : cs.[i]=ds.[i] := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ i : V, ∀ n m cs ds a b c : V, Trace n cs a b → Trace m ds a c →
      i≤n → i≤m → cs.[i]=ds.[i] := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun i : V => ∀ n m cs ds a b c : V, Trace n cs a b → Trace m ds a c →
        i≤n → i≤m → cs.[i]=ds.[i]) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb comparisonFormula,by trivial,?_⟩
      intro i; simpa using (comparison_correct i).symm
    · intro n m cs ds a b c ht gt hi hj
      exact ht.2.1.trans gt.2.1.symm
    · intro i ih n m cs ds a b c ht gt hi hj
      have hin : i<n := lt_of_lt_of_le (by simp) hi
      have him : i<m := lt_of_lt_of_le (by simp) hj
      rw [ht.2.2.2 i hin,gt.2.2.2 i him,ih n m cs ds a b c ht gt (le_of_lt hin) (le_of_lt him)]
  exact all i n m cs ds a b c h g hi hj

theorem trace_unique {n cs ds a b c : V} (h : Trace n cs a b) (g : Trace n ds a c) : b=c := by
  simpa only [h.2.2.1,g.2.2.1] using trace_agrees_at h g n (le_refl n) (le_refl n)

theorem trace_fixed_at {n cs a b : V} (h : Trace n cs a b) (hs : stepValue a=a)
    (i : V) (hi : i≤n) : cs.[i]=a := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ i : V, ∀ n cs a b : V, Trace n cs a b → stepValue a=a → i≤n → cs.[i]=a := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun i : V => ∀ n cs a b : V, Trace n cs a b → stepValue a=a → i≤n → cs.[i]=a) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb stabilityFormula,by trivial,?_⟩
      intro i; simpa using (stability_correct i).symm
    · intro n cs a b ht hs hi; exact ht.2.1
    · intro i ih n cs a b ht hs hi
      have hin : i<n := lt_of_lt_of_le (by simp) hi
      rw [ht.2.2.2 i hin,ih n cs a b ht hs (le_of_lt hin),hs]
  exact all i n cs a b h hs hi

lemma trace_stable (n a : V) (hs : stepValue a=a) : ∃ cs, Trace n cs a a := by
  obtain ⟨cs,b,h⟩ := trace_exists n a
  have he : b=a := by simpa only [h.2.2.1] using trace_fixed_at h hs n (le_refl n)
  subst b
  exact ⟨cs,h⟩

/-- Absorbing halt and deterministic model traces justify prefix transport.
No assumption that the source did not halt before the prefix is made. -/
theorem prefix_halting_iff {p ps a mid : V} (hp : Trace p ps a mid) :
    (∃ n cs b, Trace n cs a b ∧ control b=0) ↔
    (∃ n cs b, Trace n cs mid b ∧ control b=0) := by
  constructor
  · rintro ⟨n,cs,b,h,hb⟩
    have hs : stepValue b=b := by simp [stepValue,hb]
    obtain ⟨bs,hbs⟩ := trace_stable p b hs
    obtain ⟨ws,hws⟩ := trace_compose h hbs
    obtain ⟨ds,c,hd⟩ := trace_exists n mid
    obtain ⟨zs,hzs⟩ := trace_compose hp hd
    have he : c=b := trace_unique hzs (by simpa only [add_comm] using hws)
    subst c
    exact ⟨n,ds,b,hd,hb⟩
  · rintro ⟨n,cs,b,h,hb⟩
    obtain ⟨ds,hd⟩ := trace_compose hp h
    exact ⟨p+n,ds,b,hd,hb⟩
/-- A nonhalting prefix endpoint rules out every shorter-or-equal halting
trace from the same start. This is derived, never assumed. -/
theorem prefix_excludes_early_halt {p ps a mid n cs b : V}
    (hp : Trace p ps a mid) (hm : control mid≠0) (h : Trace n cs a b)
    (hn : n≤p) (hb : control b=0) : False := by
  obtain ⟨d,rfl⟩ := exists_add_of_le hn
  have hs : stepValue b=b := by simp [stepValue,hb]
  obtain ⟨bs,hbs⟩ := trace_stable d b hs
  obtain ⟨ws,hws⟩ := trace_compose h hbs
  have he : mid=b := trace_unique hp hws
  exact hm (he ▸ hb)

end Models
#print axioms trace_agrees_at
#print axioms trace_unique
#print axioms trace_fixed_at
#print axioms prefix_halting_iff
#print axioms prefix_excludes_early_halt
end PA213.PA.InternalTrace.CodedSource

