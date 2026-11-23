module
public import I3_334Support.SetTheory.Graphs.GraphUpdates
public import I3_334Support.SetTheory.Classes.ModelSyntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem natObject_iff {w : V} (omega : Internal.Omega N.mem w) (a : V) :
    Internal.NatObject N.mem a ↔ N.mem a w :=
  ⟨fun ⟨_,other,atOther⟩ => (N.omega_unique other omega) ▸ atOther,fun ha => ⟨w,omega,ha⟩⟩

/-- A natural history is a graph defined on the inclusive initial segment
of the model's natural numbers, with a fixed successor update. -/
structure NaturalHistory (step : V → V → V → Prop) (a graph w start n : V) : Prop where
  function : Internal.FunctionOn N.mem graph (N.succ n)
  initial : Internal.At N.mem graph N.empty start
  closed : ∀ i x, Internal.At N.mem graph i x → N.mem x w
  stepwise : ∀ i, N.mem i n → ∃ x y, Internal.At N.mem graph i x ∧
    Internal.At N.mem graph (N.succ i) y ∧ step a x y

variable {step : V → V → V → Prop}

theorem naturalHistory_def (stepDef : Definable.Relation3 N step)
    {k a f w s n : Nat} (ha : a < k) (hf : f < k) (hw : w < k) (hs : s < k) (hn : n < k) :
    N.square.Definable k (fun env => N.NaturalHistory step (env a) (env f) (env w) (env s) (env n)) := by
  have domain := Definable.successor (N := N) (n := k+1) (i := n+1) (j := 0) (by omega) (by omega)
  have shape := Definable.functionOn (N := N) (n := k+1) (i := f+1) (j := 0) (by omega) (by omega)
  have initial := Definable.ex ((Definable.empty (N := N) (n := k+1) (i := 0) (by omega)).and
    (Definable.graphValue (N := N) (n := k+1) (i := f+1) (j := 0) (k := s+1) (by omega) (by omega) (by omega)))
  have close := Definable.all (Definable.all
    ((Definable.graphValue (N := N) (n := k+2) (i := f+2) (j := 1) (k := 0) (by omega) (by omega) (by omega)).implies
     (Definable.mem (N := N) (n := k+2) (i := 0) (j := w+2) (by omega) (by omega))))
  have nextIndex := Definable.successor (N := N) (n := k+4) (i := 3) (j := 2) (by omega) (by omega)
  have before := Definable.graphValue (N := N) (n := k+4) (i := f+4) (j := 3) (k := 1) (by omega) (by omega) (by omega)
  have after := Definable.graphValue (N := N) (n := k+4) (i := f+4) (j := 2) (k := 0) (by omega) (by omega) (by omega)
  have update := stepDef (n := k+4) (i := a+4) (j := 1) (k := 0) (by omega) (by omega) (by omega)
  have steps := Definable.boundedAll (S := N.square) hn _
    (Definable.ex (Definable.ex (Definable.ex (nextIndex.and (before.and (after.and update))))))
  refine ((Definable.ex (domain.and shape)).and (initial.and (close.and steps))).congr fun env => ?_
  constructor
  · rintro ⟨⟨dom,next,funOn⟩,⟨zero,empty,hit⟩,closed,edits⟩
    rw [(N.internal_succ _ _).mp next] at funOn
    rw [(N.empty_unique _).mp empty] at hit
    exact ⟨funOn,hit,closed,fun i hi => by
      obtain ⟨j,x,y,succ,source,to,h⟩ := edits i hi
      rw [(N.internal_succ _ _).mp succ] at to
      exact ⟨x,y,source,to,h⟩⟩
  · intro h
    exact ⟨⟨N.succ _,N.mem_succ _,h.function⟩,⟨N.empty,N.empty_mem,h.initial⟩,h.closed,
      fun i hi => by
        obtain ⟨x,y,source,to,h⟩ := h.stepwise i hi
        exact ⟨N.succ i,x,y,N.mem_succ i,source,to,h⟩⟩

theorem naturalHistory_zero {w start a : V} (hs : N.mem start w) :
    ∃ f, N.NaturalHistory step a f w start N.empty := by
  let g := N.adjoinValue N.empty N.empty start
  have emptyFunction : Internal.FunctionOn N.mem N.empty N.empty :=
    ⟨fun x hx => (N.empty_mem x hx).elim,fun x hx => (N.empty_mem x hx).elim⟩
  have function := N.function_adjoinValue (i := N.empty) (v := start) emptyFunction (N.empty_mem _)
  rw [N.succDomain_self] at function
  refine ⟨g,function,(N.at_adjoinValue ..).mpr (Or.inr ⟨rfl,rfl⟩),fun i x h => ?_,
    fun i hi => (N.empty_mem i hi).elim⟩
  rcases (N.at_adjoinValue ..).mp h with ⟨p,hp,_⟩ | ⟨_,same⟩
  · exact (N.empty_mem p hp).elim
  · exact same.symm ▸ hs

theorem naturalHistory_extend {w start a f n : V} (omega : Internal.Omega N.mem w)
    (nIn : N.mem n w) (before : N.NaturalHistory step a f w start n)
    (total : ∀ x, N.mem x w → ∃ y, N.mem y w ∧ step a x y) :
    ∃ g, N.NaturalHistory step a g w start (N.succ n) ∧
      ∀ i x, Internal.At N.mem f i x → Internal.At N.mem g i x := by
  let dom := N.succ n
  obtain ⟨x,atOld,_⟩ := before.function.1 n ((N.mem_succ _ _).mpr (Or.inr rfl))
  obtain ⟨y,yn,transition⟩ := total x (before.closed _ _ atOld)
  let g := N.adjoinValue f dom y
  have ordinal := (N.omega_ordinal omega).of_mem N (N.omega_succ omega nIn)
  have function := N.function_adjoinValue (i := dom) (v := y) before.function (ordinal.not_mem_self N)
  rw [N.succDomain_self] at function
  have old (i v : V) (h : Internal.At N.mem f i v) : Internal.At N.mem g i v :=
    (N.at_adjoinValue ..).mpr (Or.inl h)
  refine ⟨g,⟨function,old _ _ before.initial,fun i v h => ?_,fun i hi => ?_⟩,old⟩
  · rcases (N.at_adjoinValue ..).mp h with h | ⟨_,same⟩
    · exact before.closed _ _ h
    · exact same.symm ▸ yn
  · rcases (N.mem_succ _ _).mp hi with prev | rfl
    · obtain ⟨v,z,atV,atZ,step⟩ := before.stepwise i prev
      exact ⟨v,z,old _ _ atV,old _ _ atZ,step⟩
    · exact ⟨x,y,old _ _ atOld,(N.at_adjoinValue ..).mpr (Or.inr ⟨rfl,rfl⟩),transition⟩

theorem naturalHistory_exists {w start a : V} (omega : Internal.Omega N.mem w)
    (startIn : N.mem start w) (stepDef : Definable.Relation3 N step)
    (total : ∀ x, N.mem x w → ∃ y, N.mem y w ∧ step a x y) :
    ∀ n, N.mem n w → ∃ f, N.NaturalHistory step a f w start n := by
  have defn := Definable.ex (N.naturalHistory_def stepDef
    (k := 5) (a := 2) (f := 0) (w := 3) (s := 4) (n := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide))
  exact N.omega_induction omega [w,start] defn a (N.naturalHistory_zero startIn)
    (fun n hn ⟨f,hf⟩ => by
      obtain ⟨g,hg,_⟩ := N.naturalHistory_extend omega hn hf total
      exact ⟨g,hg⟩)

theorem naturalHistory_agree {w a start f g n m : V} (omega : Internal.Omega N.mem w)
    (nf : N.mem n w) (mf : N.mem m w) (history : N.NaturalHistory step a f w start n)
    (other : N.NaturalHistory step a g w start m)
    (unique : ∀ a x y z, step a x y → step a x z → y = z) :
    ∀ i, N.mem i w → N.mem i (N.succ n) → N.mem i (N.succ m) →
      ∀ x y, Internal.At N.mem f i x → Internal.At N.mem g i y → x = y := by
  have memF := Definable.mem (N := N) (n := 5) (i := 0) (j := 1) (by decide) (by decide)
  have memG := Definable.mem (N := N) (n := 5) (i := 0) (j := 2) (by decide) (by decide)
  have atF := Definable.graphValue (N := N) (n := 7) (i := 5) (j := 2) (k := 1) (by decide) (by decide) (by decide)
  have atG := Definable.graphValue (N := N) (n := 7) (i := 6) (j := 2) (k := 0) (by decide) (by decide) (by decide)
  have eq := Definable.eq (S := N.square) (n := 7) (i := 1) (j := 0) (by decide) (by decide)
  have descr := memF.implies (memG.implies (Definable.all (Definable.all (atF.implies (atG.implies eq)))))
  apply N.omega_induction omega [N.succ m,f,g] descr (N.succ n)
  · intro _ _ x y xAt yAt
    exact (N.at_unique history.function xAt history.initial).trans (N.at_unique other.function other.initial yAt)
  · intro i hi induction_ hF hG x y endF endG
    have lower {n : V} (hn : N.mem n w) (larger : N.mem (N.succ i) (N.succ n)) : N.mem i n := by
      rcases (N.mem_succ _ _).mp larger with step | eq
      · exact ((N.omega_ordinal omega).of_mem N hn).transitive _ step _
          ((N.mem_succ _ _).mpr (Or.inr rfl))
      · exact eq ▸ (N.mem_succ i i).mpr (Or.inr rfl)
    have lf := lower nf hF
    have lg := lower mf hG
    obtain ⟨u,v,atU,atV,uv⟩ := history.stepwise i lf
    obtain ⟨s,t,atS,atT,st⟩ := other.stepwise i lg
    have starts := induction_ ((N.mem_succ _ _).mpr (Or.inl lf)) ((N.mem_succ _ _).mpr (Or.inl lg)) u s atU atS
    change u = s at starts
    subst s
    exact (N.at_unique history.function endF atV).trans
      ((unique _ _ _ _ uv st).trans (N.at_unique other.function atT endG))

end PalomarI3380.SquareRepresentation.SetContext
