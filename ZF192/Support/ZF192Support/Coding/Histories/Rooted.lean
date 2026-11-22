module
public import ZF192Support.Coding.Histories.TraceEquations
public import ZF192Support.Coding.Lists.Induction
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelScheduler
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def rootedEdge (R:M→M→Prop) (initial next tail:M) : Prop :=
 (tail=0 ∧ next=initial) ∨ (tail≠0 ∧ R (modelListHead tail) next)
def rooted (R:M→M→Prop) (initial code:M) : Prop := code≠0 ∧ modelTrace (rootedEdge R initial) code
def rootedFormula {ξ : Type} (rel:ArithmeticSemiformula ξ 2) : ArithmeticSemiformula ξ 2 :=
 “initial n. n≠0 ∧ !(Rewriting.emb tailIterationGraph.val) 0 n n ∧ ∀k<n, ∃g, !(Rewriting.emb tailIterationGraph.val) g k n ∧
 (g=0 ∨ ∃a, ∃b, !(Rewriting.emb listHeadGraph.val) a g ∧ !(Rewriting.emb listTailGraph.val) b g ∧
 ((b=0 ∧ a=initial) ∨ (b≠0 ∧ ∃prev, !(Rewriting.emb listHeadGraph.val) prev b ∧ !rel prev a)))”
lemma rootedFormula_eval {ξ : Type} (rel:ArithmeticSemiformula ξ 2) (ρ:ξ→M) (R:M→M→Prop)
 (hr:∀a b,rel.Eval ![a,b] ρ ↔ R a b) (initial code:M) :
 (rootedFormula rel).Eval ![initial,code] ρ ↔ rooted R initial code := by
 simp [rootedFormula,rooted,rootedEdge,modelTrace,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,tailIterationGraph_defined.iff,
 ruleHead_defined.iff,ruleTail_defined.iff,hr,eq_comm]
lemma rooted_singleton (R:M→M→Prop) (initial:M) : rooted R initial (modelListCons initial 0) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨modelTrace_zero _,Or.inl ⟨rfl,rfl⟩⟩
lemma rooted_extend (R:M→M→Prop) {initial code next:M} (h:rooted R initial code)
 (hs:R (modelListHead code) next) : rooted R initial (modelListCons next code) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨h.2,Or.inr ⟨h.1,hs⟩⟩
/-- Induction on rooted histories, with a first-order definition of the induction property. -/
lemma rooted_induction (R : M → M → Prop) (initial : M)
    (φ : ArithmeticSemiformula Nat 1) (ρ : Nat → M) (P : M → Prop)
    (hP : ∀ n, φ.Eval ![n] ρ ↔ (rooted R initial n → P (modelListHead n)))
    (base : P initial) (step : ∀ a b, R a b → P a → P b)
    (n : M) (hr : rooted R initial n) : P (modelListHead n) := by
  refine (ZF192Support.ModelOperationalConcat.model_list_induction φ ρ
    (fun n => rooted R initial n → P (modelListHead n)) hP (by simp [rooted]) ?_ n hr)
  intro a b ih hab
  rw [modelListHead_cons]
  obtain ⟨htrace, hedge⟩ := (modelTrace_cons _ _ _).mp hab.2
  rcases hedge with ⟨_, rfl⟩ | ⟨hb, hs⟩
  · exact base
  · exact step _ _ hs (ih ⟨hb, htrace⟩)

/-- Over the standard naturals an invariant of a coded history need not be arithmetical. -/
theorem rooted_nat_induction {R : Nat → Nat → Prop} {initial code : Nat}
    (hr : rooted R initial code) {P : Nat → Prop} (base : P initial)
    (step : ∀ {a b}, R a b → P a → P b) : P (modelListHead code) := by
  induction code using Nat.strongRecOn with
  | ind code ih =>
    have pos := Nat.pos_of_ne_zero hr.1
    have trace := hr.2
    rw [← modelList_reconstruct code pos, modelTrace_cons] at trace
    rcases trace.2 with ⟨_, eq⟩ | ⟨hne, hstep⟩
    · exact eq.symm ▸ base
    · exact step hstep (ih _ (modelListTail_lt code pos) ⟨hne, trace.1⟩)

end ZF192Support.ModelScheduler
