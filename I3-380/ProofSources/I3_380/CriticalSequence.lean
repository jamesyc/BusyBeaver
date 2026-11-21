module
public import I3_380.OmegaIteration
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

/-- An internally set-coded sequence following the class graph of J. -/
structure JSequence (w graph : V) : Prop where
  functionOn : Internal.FunctionOn N.mem graph w
  active : ∀ n a, Internal.At N.mem graph n a → N.square.activePoint a
  next : ∀ n a b, N.mem n w → Internal.At N.mem graph n a → Internal.At N.mem graph (N.succ n) b →
    N.square.rel (M.constant .J) a b

theorem JSequence.image {N : NamedModel M V} {w f n : V} (seq : N.JSequence w f)
    {a b : N.Active} (inW : N.mem n w) (fa : Internal.At N.mem f n a.val)
    (fb : Internal.At N.mem f (N.succ n) b.val) : N.embedding a = b :=
  Subtype.ext (j_single_valued N.laws N.active_closure (N.embedding_edge a) (seq.next _ _ _ inW fa fb))

theorem JSequence.adjacent {N : NamedModel M V} {w f : V} (seq : N.JSequence w f)
    (omega : Internal.Omega N.mem w) (key : V) {R : V → V → V → Prop}
    (defn : Definable.Relation3 N.toSetContext R)
    (stable : ∀ x y : N.Active, R key x.val y.val → R key (N.embedding x).val (N.embedding y).val)
    (base : ∀ x y, Internal.At N.mem f N.empty x → Internal.At N.mem f (N.succ N.empty) y → R key x y) :
    ∀ n, N.mem n w → ∀ x y, Internal.At N.mem f n x → Internal.At N.mem f (N.succ n) y → R key x y := by
  have successor := Definable.successor (N := N.toSetContext) (n := 5) (i := 1) (j := 0) (by decide) (by decide)
  have first := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 5) (j := 3) (k := 1)
    (by decide) (by decide) (by decide)
  have second := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 5) (j := 2) (k := 0)
    (by decide) (by decide) (by decide)
  have desc := Definable.ex (successor.and (Definable.all (Definable.all
    (first.implies (second.implies (defn (n := 7) (i := 6) (j := 1) (k := 0)
      (by decide) (by decide) (by decide)))))))
  have all : ∀ n, N.mem n w → ∃ next, Internal.Succ N.mem n next ∧
      ∀ x y, Internal.At N.mem f n x → Internal.At N.mem f next y → R key x y := by
    apply N.omega_induction omega [f,key] desc w
    · exact ⟨N.succ N.empty, N.mem_succ _, base⟩
    · intro n inW ih
      obtain ⟨next, relation, earlier⟩ := ih
      have shift : next = N.succ n := (N.internal_succ _ _).mp relation
      subst next
      refine ⟨N.succ (N.succ n), N.mem_succ _, fun a b hA hB => ?_⟩
      obtain ⟨previous, hPrev, _⟩ := seq.functionOn.1 n inW
      let x : N.Active := ⟨previous, seq.active n previous hPrev⟩
      let y : N.Active := ⟨a, seq.active (N.succ n) a hA⟩
      let z : N.Active := ⟨b, seq.active (N.succ (N.succ n)) b hB⟩
      have fx := seq.image (a := x) (b := y) inW hPrev hA
      have fy := seq.image (a := y) (b := z) (N.omega_succ omega inW) hA hB
      have carried := stable x y (earlier previous a hPrev hA)
      rw [fx,fy] at carried
      exact carried
  intro n inW x y hx hy
  obtain ⟨m, hm, h⟩ := all n inW
  have eq := (N.internal_succ _ _).mp hm
  subst m
  exact h x y hx hy

theorem JSequence.baseAdjacent {N : NamedModel M V} {w f : V} (seq : N.JSequence w f)
    (omega : Internal.Omega N.mem w) (base : N.Active) (initial : Internal.At N.mem f N.empty base.val)
    {R : V → V → Prop} (first : R base.val (N.embedding base).val) :
    ∀ x y, Internal.At N.mem f N.empty x → Internal.At N.mem f (N.succ N.empty) y → R x y := by
  intro x y hx hy
  have inW := N.omega_zero omega
  obtain ⟨_, _, one⟩ := seq.functionOn.1 N.empty inW
  have eq := (one x hx).trans (one base.val initial).symm
  subst x
  let next : N.Active := ⟨y, seq.active (N.succ N.empty) y hy⟩
  have h := seq.image (a := base) (b := next) inW initial hy
  rw [h] at first
  exact first

structure CriticalRun (w heights stages : V) : Prop where
  heightSequence : N.JSequence w heights
  stageSequence : N.JSequence w stages
  ranks : ∀ n a s, Internal.At N.mem heights n a → Internal.At N.mem stages n s → N.Rank a s
  increasing : ∀ n, N.mem n w → ∀ a b,
    Internal.At N.mem heights n a → Internal.At N.mem heights (N.succ n) b → N.mem a b
  elementary : ∀ n, N.mem n w → ∀ a b,
    Internal.At N.mem stages n a → Internal.At N.mem stages (N.succ n) b →
      Internal.ElementaryIncluded N.mem w a b

theorem critical_run {w : V} (omega : Internal.Omega N.mem w) (wActive : N.square.activePoint w)
    {point stage : N.Active} (crit : N.Critical point stage) :
    ∃ heights stages, N.CriticalRun w heights stages ∧
      Internal.At N.mem heights N.empty point.val ∧ Internal.At N.mem stages N.empty stage.val := by
  obtain ⟨heights, hH, firstHeight, typed, follows⟩ := N.ordinal_iterates omega point crit.rank.1
  have hSeq : N.JSequence w heights := ⟨hH, fun n a h => (typed n a h).1, follows⟩
  have has := Definable.graphValue (N := N.toSetContext) (n := 4) (i := 3) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have rank := Definable.rank (N := N.toSetContext) (n := 4) (i := 0) (j := 2) (by decide) (by decide)
  have predicate := Definable.ex (has.and rank)
  have unique (n x y : V)
      (hx : ∃ a, Internal.At N.mem heights n a ∧ N.Rank a x)
      (hy : ∃ b, Internal.At N.mem heights n b ∧ N.Rank b y) : x = y := by
    obtain ⟨a, atA, rankA⟩ := hx
    obtain ⟨b, atB, rankB⟩ := hy
    obtain ⟨_,_,one⟩ := hH.1 n (SetRecursion.at_domain hH atA)
    have eq := (one a atA).trans (one b atB).symm
    subst b
    exact N.rank_unique rankA rankB
  have total (n : V) (inW : N.mem n w) :
      ∃ result a, Internal.At N.mem heights n a ∧ N.Rank a result := by
    obtain ⟨a, ha, _⟩ := hH.1 n inW
    obtain ⟨stage, value⟩ := N.rank_exists (typed _ _ ha).2
    exact ⟨stage,a,ha,value⟩
  obtain ⟨stages, hS, values⟩ := N.functionOf [heights] predicate unique w total
  have both {n a s : V} (h : Internal.At N.mem heights n a) (hs : Internal.At N.mem stages n s) : N.Rank a s := by
    obtain ⟨inW,b,hb,rank⟩ := (values n s).mp hs
    obtain ⟨_,_,one⟩ := hH.1 n inW
    have eq := (one b hb).trans (one a h).symm
    exact eq ▸ rank
  have active (n s : V) (edge : Internal.At N.mem stages n s) : N.square.activePoint s := by
    obtain ⟨_,a,ha,pair⟩ := (values n s).mp edge
    exact N.active_rank_value (typed _ _ ha).1 pair
  have firstStage : Internal.At N.mem stages N.empty stage.val := (values _ _).mpr
    ⟨N.omega_zero omega, point.val, firstHeight, crit.rank⟩
  have stageSeq : N.JSequence w stages := by
    refine ⟨hS, active, fun n a b inW fa fb => ?_⟩
    obtain ⟨x, hx, _⟩ := hH.1 n inW
    obtain ⟨y, hy, _⟩ := hH.1 (N.succ n) (N.omega_succ omega inW)
    let s : N.Active := ⟨a, active n a fa⟩
    let t : N.Active := ⟨b, active (N.succ n) b fb⟩
    let h₁ : N.Active := ⟨x, (typed _ _ hx).1⟩
    let h₂ : N.Active := ⟨y, (typed _ _ hy).1⟩
    have step := hSeq.image (a := h₁) (b := h₂) inW hx hy
    have image := (N.preserves_rank h₁ s).mp (both hx fa)
    rw [step] at image
    have same : N.embedding s = t := Subtype.ext (N.rank_unique image (both hy fb))
    have connected := N.embedding_edge s
    rw [same] at connected
    exact connected
  have increasing := hSeq.adjacent omega w (R := fun _ => N.mem) Definable.membership_relation
    (fun x y => (N.preserves_membership x y).mp) (hSeq.baseAdjacent omega point firstHeight crit.movesUp)
  let omegaNode : N.Active := ⟨w,wActive⟩
  have elementary := stageSeq.adjacent omega w (R := Internal.ElementaryIncluded N.mem)
    (fun h₁ h₂ h₃ => Definable.elementaryIncluded h₁ h₂ h₃)
    (fun x y => (N.preserves_elementaryIncluded omegaNode x y omega).mp)
    (stageSeq.baseAdjacent omega stage firstStage (N.critical_elementary omega wActive crit))
  exact ⟨heights, stages, ⟨hSeq, stageSeq, fun _ _ _ => both, increasing, elementary⟩, firstHeight, firstStage⟩

end PalomarI3380.SquareRepresentation.NamedModel
