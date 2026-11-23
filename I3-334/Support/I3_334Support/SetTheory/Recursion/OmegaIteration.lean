module
public import I3_334Support.SetTheory.Rank.ElementaryStages
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)


theorem successor_predecessor_unique {a b successor : V} (o : N.Ordinal successor)
    (left : Internal.Succ N.mem a successor) (right : Internal.Succ N.mem b successor) : a = b := by
  have aIn := (left a).mpr (Or.inr rfl)
  have bIn := (right b).mpr (Or.inr rfl)
  rcases o.ordered.compare a b aIn bIn with less | eq | greater
  · have atSucc := (right b).mpr (Or.inr rfl)
    rcases (left b).mp atSucc with bad | eq
    · exact (WellOrderOn.asymm N.toSetContext o.ordered aIn bIn less bad).elim
    · exact eq.symm
  · exact eq
  · have atSucc := (left a).mpr (Or.inr rfl)
    rcases (right a).mp atSucc with bad | eq
    · exact (WellOrderOn.asymm N.toSetContext o.ordered bIn aIn greater bad).elim
    · exact eq

def PriorImage (i prior x : V) : Prop :=
  ∃ index, Internal.Succ N.mem index i ∧ Internal.At N.mem prior index x ∧ N.square.activePoint x

def OnlyPriorImage (i prior x : V) : Prop :=
  N.PriorImage i prior x ∧ ∀ y, N.PriorImage i prior y → y = x

def IterateStep (start i prior next : V) : Prop :=
  (∃ x, N.OnlyPriorImage i prior x ∧ N.square.rel (M.constant .J) x next) ∨
    (¬∃ x, N.OnlyPriorImage i prior x) ∧ next = start

theorem priorImage_def {n i f x : Nat} (hi : i < n) (hf : f < n) (hx : x < n) :
    N.square.Definable n (fun env => N.PriorImage (env i) (env f) (env x)) := by
  have ord := Definable.successor (N := N.toSetContext) (n := n + 1) (i := 0) (j := i + 1) (by omega) (by omega)
  have lookup := Definable.graphValue (N := N.toSetContext) (n := n + 1) (i := f + 1) (j := 0) (k := x + 1)
    (by omega) (by omega) (by omega)
  have active := Definable.active (N := N) (n := n + 1) (i := x + 1) (by omega)
  exact Definable.ex (ord.and (lookup.and active))

theorem onlyPriorImage_def {n i f x : Nat} (hi : i < n) (hf : f < n) (hx : x < n) :
    N.square.Definable n (fun env => N.OnlyPriorImage (env i) (env f) (env x)) := by
  have prior := N.priorImage_def (n := n + 1) (i := i + 1) (f := f + 1) (x := 0) (by omega) (by omega) (by omega)
  have same := Definable.eq (S := N.square) (n := n + 1) (i := 0) (j := x + 1) (by omega) (by omega)
  exact (N.priorImage_def hi hf hx).and (Definable.all (prior.implies same))

theorem iterateStep_def : Definable.Relation4 N.toSetContext (N.IterateStep) := by
  intro n s i f t hs hi hf ht
  have prior := N.onlyPriorImage_def (n := n + 1) (i := i + 1) (f := f + 1) (x := 0)
    (by omega) (by omega) (by omega)
  have edge := Definable.atom (S := N.square) (n := n + 1) (M.constant .J) (i := 0) (j := t + 1)
    (by omega) (by omega)
  have same := Definable.eq (S := N.square) (n := n) (i := t) (j := s) ht hs
  exact (Definable.ex (prior.and edge)).or ((Definable.ex prior).not.and same)

theorem iterateStep_exists (start i prior : V) : ∃ next, N.IterateStep start i prior next := by
  classical
  by_cases candidate : ∃ x, N.OnlyPriorImage i prior x
  · obtain ⟨x, hx⟩ := candidate
    obtain ⟨_, _, _, active⟩ := hx.1
    obtain ⟨y, hy⟩ := j_has_image N.laws ⟨x, active⟩
    exact ⟨y, Or.inl ⟨x, hx, hy⟩⟩
  · exact ⟨start, Or.inr ⟨candidate, rfl⟩⟩

theorem iterateStep_unique (start i prior u v : V)
    (left : N.IterateStep start i prior u) (right : N.IterateStep start i prior v) : u = v := by
  rcases left with ⟨x,hx,hxy⟩ | ⟨no₁, eq₁⟩ <;>
    rcases right with ⟨y,hy,hyz⟩ | ⟨no₂, eq₂⟩
  · have eq : y = x := hx.2 y hy.1
    subst y
    exact j_single_valued N.laws N.active_closure hxy hyz
  · exact (no₂ ⟨x,hx⟩).elim
  · exact (no₁ ⟨y,hy⟩).elim
  · exact eq₁.trans eq₂.symm

noncomputable def iterateRecursor (w start : V) (omega : Internal.Omega N.mem w) : SetRecursion N.toSetContext :=
  ⟨w, w, start, fun _ => N.mem, Definable.membership_relation, (N.omega_ordinal omega).ordered,
    N.IterateStep, N.iterateStep_def, N.iterateStep_exists start, N.iterateStep_unique start⟩

theorem iterate_zero {w start graph : V} {omega : Internal.Omega N.mem w}
    (sol : (N.iterateRecursor w start omega).Solution w graph) :
    Internal.At N.mem graph N.empty start := by
  obtain ⟨cut, prior, value, _, restrict, holdsAt, rule⟩ := sol.agrees N.empty (N.omega_zero omega)
  rcases rule with ⟨x, h, edge⟩ | ⟨_, eq⟩
  · obtain ⟨earlier, step, _, _⟩ := h.1
    exact (N.empty_mem earlier ((step earlier).mpr (Or.inr rfl))).elim
  · change value = start at eq
    exact eq ▸ holdsAt

theorem iterate_successor {w start graph n a b : V} {omega : Internal.Omega N.mem w}
    (sol : (N.iterateRecursor w start omega).Solution w graph) (nIn : N.mem n w)
    (source : Internal.At N.mem graph n a) (target : Internal.At N.mem graph (N.succ n) b)
    (active : N.square.activePoint a) :
    N.square.rel (M.constant .J) a b := by
  have nextIn := N.omega_succ omega nIn
  have ord := (N.omega_ordinal omega).of_mem N.toSetContext nextIn
  obtain ⟨cut, prior, value, desc, previous, v, rule⟩ := sol.agrees (N.succ n) nextIn
  obtain ⟨_, _, one⟩ := sol.functionOn.1 (N.succ n) nextIn
  have valueEq := (one value v).trans (one b target).symm
  subst value
  have nPrior : N.mem n cut := (desc n).mpr ⟨nIn, (N.mem_succ _ _).mpr (Or.inr rfl)⟩
  have before : N.PriorImage (N.succ n) prior a :=
    ⟨n, N.mem_succ n, (N.restricts_value previous).mpr ⟨nPrior, source⟩, active⟩
  have only : N.OnlyPriorImage (N.succ n) prior a := by
    refine ⟨before, fun y hy => ?_⟩
    obtain ⟨m, step, earlier, activeY⟩ := hy
    have same := N.successor_predecessor_unique ord step (N.mem_succ n)
    subst m
    have atN := ((N.restricts_value previous).mp earlier).2
    obtain ⟨_, _, unique⟩ := sol.functionOn.1 n nIn
    exact (unique y atN).trans (unique a source).symm
  rcases rule with ⟨x,h,edge⟩ | ⟨no,eq⟩
  · exact (only.2 x h.1) ▸ edge
  · exact (no ⟨a,only⟩).elim

/-- The iterates of the embedding on any active ordinal form one actual
set graph with the model's own omega as its domain. -/
theorem ordinal_iterates {w : V} (omega : Internal.Omega N.mem w) (start : N.Active)
    (ordinal : N.Ordinal start.val) :
    ∃ graph, Internal.FunctionOn N.mem graph w ∧ Internal.At N.mem graph N.empty start.val ∧
      (∀ n a, Internal.At N.mem graph n a → N.square.activePoint a ∧ N.Ordinal a) ∧
      ∀ n a b, N.mem n w → Internal.At N.mem graph n a → Internal.At N.mem graph (N.succ n) b →
        N.square.rel (M.constant .J) a b := by
  obtain ⟨graph, solution⟩ := (N.iterateRecursor w start.val omega).solution_exists
  have atZero := N.iterate_zero solution
  have desc := Definable.all ((Definable.graphValue (N := N.toSetContext) (n := 4) (i := 3) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)).implies
      ((Definable.active (N := N) (n := 4) (i := 0) (by decide)).and
        (Definable.ordinal (N := N.toSetContext) (n := 4) (i := 0) (by decide))))
  have typed : ∀ n, N.mem n w → ∀ a, Internal.At N.mem graph n a → N.square.activePoint a ∧ N.Ordinal a := by
    apply N.omega_induction omega [graph] desc w
    · intro a atA
      obtain ⟨_, _, one⟩ := solution.functionOn.1 N.empty (N.omega_zero omega)
      have eq := (one a atA).trans (one start.val atZero).symm
      exact eq.symm ▸ ⟨start.property, ordinal⟩
    · intro n nIn ih b edge
      obtain ⟨a, atA, _⟩ := solution.functionOn.1 n nIn
      obtain ⟨activeA, ordA⟩ := ih a atA
      have relation := N.iterate_successor solution nIn atA edge activeA
      have activeB := (j_active N.laws N.active_closure relation).2
      let x : N.Active := ⟨a, activeA⟩
      have eq := j_single_valued N.laws N.active_closure (N.embedding_edge x) relation
      exact ⟨activeB, eq ▸ (N.preserves_ordinal x).mp ordA⟩
  have all (n a : V) (ha : Internal.At N.mem graph n a) : N.square.activePoint a ∧ N.Ordinal a :=
    typed n (SetRecursion.at_domain solution.functionOn ha) a ha
  exact ⟨graph, solution.functionOn, atZero, all, fun n a b inW source target =>
    N.iterate_successor solution inW source target (all n a source).1⟩

end PalomarI3380.SquareRepresentation.NamedModel
