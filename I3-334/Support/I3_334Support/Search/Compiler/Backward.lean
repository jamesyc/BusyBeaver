module
public import I3_334Support.Search.Compiler.Forward
public import I3_334Support.Search.Compiler.Optimization
@[expose] public section

namespace PalomarI3380.Compiler

open Engine (incrementReversed stripThrough)

private inductive HaltsIn (root : Program) : Nat → PathState → Prop where
  | stop : step root s = none → HaltsIn root 0 s
  | advance : step root s = some t → HaltsIn root n t → HaltsIn root (n + 1) s

private theorem exists_halt_length {root : Program} {s : PathState}
    (h : Terminates (step root) s) : ∃ n, HaltsIn root n s := by
  induction h with
  | stop h => exact ⟨0, .stop h⟩
  | advance h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .advance h hn⟩

private def Remaining (root : Program) (n : Nat) (path : List Bool) (out : Flow) (t : Store) : Prop :=
  out ≠ .halt → ∃ k, k < n ∧ HaltsIn root k (atPath (destination path out) t)

private theorem transfer_left (p : List Bool) {f out : Flow} (h : f.fromLeft = some out)
    (nonhalt : out ≠ .halt) (s : Store) :
    f ≠ .halt ∧ atPath (destination (p ++ [false]) f) s = atPath (destination p out) s := by
  cases f with
  | normal => simp [Flow.fromLeft] at h
  | halt => cases h; contradiction
  | repeatAt k =>
    cases h
    simp [destination, stripMany_miss (by decide : false ≠ true)]
  | escape k =>
    cases k with
    | zero =>
      cases h
      simp [destination, stripMany, stripThrough, incrementPath]
    | succ k =>
      cases h
      simp [destination, stripMany_hit]

private theorem transfer_right (p : List Bool) {f out : Flow} (h : f.fromRight = some out)
    (nonhalt : out ≠ .halt) (s : Store) :
    f ≠ .halt ∧ atPath (destination (p ++ [true]) f) s = atPath (destination p out) s := by
  cases f with
  | halt => cases h; contradiction
  | normal =>
    cases h
    simp [destination, increment_right, atPath, trimPC_append_zero]
  | escape k =>
    cases h
    simp [destination, stripMany_miss (by decide : true ≠ false)]
  | repeatAt k =>
    cases k with
    | zero => simp [Flow.fromRight] at h
    | succ k =>
      cases h
      simp [destination, stripMany_hit]

private theorem continue_right (p : List Bool) :
    destination (p ++ [true]) (.repeatAt 0) = p := by
  simp [destination, stripMany, stripThrough]

private theorem halts_leaf {root : Program} {p : List Bool} {op : Op} {s : Store} {n : Nat}
    (located : locate root p = some (.op op)) (halted : HaltsIn root n (atPath p s)) :
    Remaining root n p (op.effect s).1 (op.effect s).2 := by
  intro nonhalt
  have stepEq := step_at_op located s
  rw [ite_eq_right nonhalt] at stepEq
  cases halted with
  | stop h => rw [stepEq] at h; contradiction
  | @advance _ _ k h next =>
    rw [stepEq, Option.some.injEq] at h
    exact ⟨k, Nat.lt_succ_self k, h ▸ next⟩

/-- Invert a finite halting run. It either halts in the current subtree
or exits it with a smaller remaining run. The inner induction follows
the left edge before consuming a machine step. -/
private theorem recover {root : Program} : ∀ (n : Nat) (tree : Program) (p : List Bool) (s : Store),
    locate root p = some tree → HaltsIn root n (atPath p s) →
    ∃ out t, Executes tree s out t ∧ Remaining root n p out t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro tree
    induction tree with
    | op op =>
      intro p s located halted
      exact ⟨_, _, .instruction _ _, halts_leaf located halted⟩
    | seq left right ihLeft _ =>
      intro p s located halted
      have sameStart : atPath (p ++ [false]) s = atPath p s := by
        simp [atPath, trimPC_append_zero]
      obtain ⟨f, middle, runLeft, remainsLeft⟩ :=
        ihLeft (p ++ [false]) s (locate_left located) (sameStart.symm ▸ halted)
      cases hLeft : f.fromLeft with
      | some out =>
        refine ⟨out, middle, .leftExit runLeft hLeft, fun nonhalt => ?_⟩
        obtain ⟨ne, same⟩ := transfer_left p hLeft nonhalt middle
        rw [← same]
        exact remainsLeft ne
      | none =>
        have normal : f = .normal := by
          cases f with
          | escape n => cases n <;> simp [Flow.fromLeft] at hLeft
          | normal => rfl
          | halt | repeatAt => simp [Flow.fromLeft] at hLeft
        subst f
        obtain ⟨k, less, tail⟩ := remainsLeft (by decide)
        rw [destination, increment_left] at tail
        obtain ⟨g, next, runRight, remainsRight⟩ :=
          ih k less right (p ++ [true]) middle (locate_right located) tail
        cases hRight : g.fromRight with
        | some out =>
          refine ⟨out, next, .rightExit runLeft runRight hRight, fun nonhalt => ?_⟩
          obtain ⟨ne, same⟩ := transfer_right p hRight nonhalt next
          obtain ⟨l, lt, rest⟩ := remainsRight ne
          exact ⟨l, Nat.lt_trans lt less, same ▸ rest⟩
        | none =>
          have repeated : g = .repeatAt 0 := by
            cases g with
            | repeatAt count => cases count <;> simp_all [Flow.fromRight]
            | normal | escape | halt => simp [Flow.fromRight] at hRight
          subst g
          obtain ⟨l, lt, rest⟩ := remainsRight (by decide)
          rw [continue_right] at rest
          have lower := Nat.lt_trans lt less
          obtain ⟨out, finish, again, remainsAgain⟩ := ih l lower _ p next located rest
          exact ⟨out, finish, .reenter runLeft runRight again, fun nonhalt => by
            obtain ⟨j, lt', tail'⟩ := remainsAgain nonhalt
            exact ⟨j, Nat.lt_trans lt' lower, tail'⟩⟩

/-- Normal completion of a closed main program restarts it at the root. -/
inductive IteratesToHalt (p : Program) : Store → Prop where
  | halt : Executes p s .halt t → IteratesToHalt p s
  | next : Executes p s .normal t → IteratesToHalt p t → IteratesToHalt p s

theorem halts_iff_iterations (p : Program) (closed : p.closed) (s : Store) :
    Terminates (step p) (atPath [] s) ↔ IteratesToHalt p s := by
  constructor
  · intro h
    obtain ⟨n, finite⟩ := exists_halt_length h
    clear h
    induction n using Nat.strongRecOn generalizing s with
    | ind n ih =>
      obtain ⟨out, t, exec, rem⟩ := recover n p [] s rfl finite
      rcases exec.closed_flow closed with rfl | rfl
      · obtain ⟨k, less, tail⟩ := rem (by decide)
        exact .next exec (ih k less t tail)
      · exact .halt exec
  · intro h
    induction h with
    | halt exec => exact exec.realizes [] rfl
    | next exec _ ih =>
      obtain ⟨_, next, path⟩ := exec.realizes [] rfl
      exact (Moves.edge next path).prepend_halt ih

theorem Equivalent.iterates {p q : Program} (h : Equivalent p q) (s : Store) :
    IteratesToHalt p s ↔ IteratesToHalt q s := by
  have transfer {p q : Program} (h : Equivalent p q) {s : Store} (run : IteratesToHalt p s) :
      IteratesToHalt q s := by
    induction run with
    | halt run => exact .halt ((h _ _ _).mp run)
    | next run _ ih => exact .next ((h _ _ _).mp run) ih
  exact ⟨transfer h, transfer h.symm⟩

end PalomarI3380.Compiler
