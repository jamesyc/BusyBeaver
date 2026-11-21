module
public import I3_380.RankOrder
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def SumOrder (domain first second x y : V) : Prop :=
  (N.mem x domain ∧ N.mem y domain ∧ Internal.At N.mem first x y) ∨
  (N.mem x domain ∧ ¬N.mem y domain) ∨
  (¬N.mem x domain ∧ ¬N.mem y domain ∧ Internal.At N.mem second x y)

theorem sumOrder_def {n d f g x y : Nat}
    (hd : d < n) (hf : f < n) (hg : g < n) (hx : x < n) (hy : y < n) :
    N.square.Definable n (fun env => N.SumOrder (env d) (env f) (env g) (env x) (env y)) := by
  have left := Definable.mem (N := N) hx hd
  have right := Definable.mem (N := N) hy hd
  have first := Definable.graphValue (N := N) hf hx hy
  have next := Definable.graphValue (N := N) hg hx hy
  exact (left.and (right.and first)).or ((left.and right.not).or (left.not.and (right.not.and next)))

theorem sumOrder_order {a b f g : V}
    (before : N.WellOrderOn (Internal.At N.mem f) a)
    (extra : N.WellOrderOn (Internal.At N.mem g) (N.difference b a)) :
    N.WellOrderOn (N.SumOrder a f g) b := by
  classical
  have outside (x : V) (hb : N.mem x b) (ha : ¬N.mem x a) : N.mem x (N.difference b a) :=
    (N.mem_difference _ _ _).mpr ⟨hb,ha⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    by_cases left : N.mem x a
    · simpa [SumOrder,left] using before.irrefl x left
    · simpa [SumOrder,left] using extra.irrefl x (outside x hx left)
  · intro x y z xb yb zb first next
    by_cases xl : N.mem x a <;> by_cases yl : N.mem y a <;> by_cases zl : N.mem z a <;>
      simp [SumOrder,xl,yl,zl] at first next ⊢
    · exact before.trans x y z xl yl zl first next
    · exact extra.trans x y z (outside x xb xl) (outside y yb yl) (outside z zb zl) first next
  · intro x y xb yb
    by_cases xl : N.mem x a <;> by_cases yl : N.mem y a <;> simp [SumOrder,xl,yl]
    · exact before.compare x y xl yl
    · exact extra.compare x y (outside x xb xl) (outside y yb yl)
  · intro requested included inhabited
    by_cases someLeft : N.NonemptySet (N.inter requested a)
    · have aBound : N.Subset (N.inter requested a) a := fun x hx => ((N.mem_inter _ _ _).mp hx).2
      obtain ⟨x,hx,minimum⟩ := before.least _ aBound someLeft
      have ⟨matchX,left⟩ := (N.mem_inter _ _ _).mp hx
      refine ⟨x,matchX,fun y hy => ?_⟩
      by_cases leftY : N.mem y a
      · exact (minimum y ((N.mem_inter _ _ _).mpr ⟨hy,leftY⟩)).elim Or.inl
          (fun h => Or.inr (Or.inl ⟨left,leftY,h⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨left,leftY⟩))
    · have outsideAll (x : V) (hx : N.mem x requested) : ¬N.mem x a :=
        fun h => someLeft ⟨x,(N.mem_inter _ _ _).mpr ⟨hx,h⟩⟩
      have extraBound : N.Subset requested (N.difference b a) :=
        fun x hx => outside x (included x hx) (outsideAll x hx)
      obtain ⟨x, hx, minimum⟩ := extra.least requested extraBound inhabited
      refine ⟨x,hx,fun y hy => ?_⟩
      exact (minimum y hy).elim Or.inl
        (fun h => Or.inr (Or.inr (Or.inr ⟨outsideAll x hx,outsideAll y hy,h⟩)))

theorem WellOrderOn.congr {N : SetContext M V} {a : V} {r s : V → V → Prop}
    (h : N.WellOrderOn r a) (same : ∀ x y, N.mem x a → N.mem y a → (r x y ↔ s x y)) :
    N.WellOrderOn s a where
  irrefl x hx hs := h.irrefl x hx ((same x x hx hx).mpr hs)
  trans x y z hx hy hz first next :=
    (same x z hx hz).mp (h.trans x y z hx hy hz ((same x y hx hy).mpr first) ((same y z hy hz).mpr next))
  compare x y hx hy := (or_congr (same x y hx hy) (or_congr Iff.rfl (same y x hy hx))).mp (h.compare x y hx hy)
  least b subset some := by
    obtain ⟨x,hx,least⟩ := h.least b subset some
    exact ⟨x,hx,fun y hy => (or_congr Iff.rfl (same x y (subset x hx) (subset y hy))).mp (least y hy)⟩

theorem extend_rankOrder {p a old f b stage : V} (before : N.RankOrder p a old f)
    (next : N.Rank b stage) (sub : N.Subset a b) :
    ∃ q graph, N.RankOrder q b stage graph ∧ N.Refines q p := by
  have inclusion := N.rank_subset before.ranked next sub
  obtain ⟨later, extra⟩ := N.wellOrdering (N.difference stage old)
  have defn := N.sumOrder_def (n := 5) (d := 2) (f := 3) (g := 4) (x := 0) (y := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨graph, described, shaped⟩ := N.binary_graph [old,f,later] defn stage stage
  let code := N.orderedPair b graph
  have direction (x y : V) (hx : N.mem x stage) (hy : N.mem y stage) :
      N.SumOrder old f later x y ↔ Internal.At N.mem graph x y :=
    ⟨fun h => (described x y).mpr ⟨hx,hy,h⟩, fun h => ((described x y).mp h).2.2⟩
  have newOrder := (N.sumOrder_order before.order extra).congr direction
  have shape : N.RelationOn graph stage := by
    intro pair hp
    obtain ⟨x,y,hx,hy,_,pCode⟩ := shaped pair hp
    exact ⟨x,y,hx,hy,pCode⟩
  have cond : N.RankOrder code b stage graph :=
    ⟨N.orderedPair_intro _ _, next, newOrder, shape⟩
  have extension : N.EndExtends a old f b stage graph := by
    refine ⟨sub,fun x hx y hy => ?_,fun x hx y hy notOld => ?_⟩
    · refine Iff.trans ?_ (direction x y (inclusion x hx) (inclusion y hy))
      simp [SumOrder,hx,hy]
    · exact (direction x y (inclusion x hx) hy).mp (Or.inr (Or.inl ⟨hx,notOld⟩))
  exact ⟨code,graph,cond,a,old,f,b,stage,graph,before,cond,extension⟩

theorem any_rankOrder {a stage : V} (ranked : N.Rank a stage) :
    ∃ code graph, N.RankOrder code a stage graph := by
  obtain ⟨r, ordered⟩ := N.wellOrdering stage
  have definition := Definable.graphValue (N := N) (n := 3) (i := 2) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  obtain ⟨g, contents, shaped⟩ := N.binary_graph [r] definition stage stage
  have exactness (x y : V) (hx : N.mem x stage) (hy : N.mem y stage) :
      Internal.At N.mem r x y ↔ Internal.At N.mem g x y :=
    ⟨fun h => (contents x y).mpr ⟨hx,hy,h⟩, fun h => ((contents x y).mp h).2.2⟩
  exact ⟨N.orderedPair a g,g,N.orderedPair_intro _ _,ranked,ordered.congr exactness,fun p hp =>
    let ⟨x,y,hx,hy,_,pair⟩ := shaped p hp; ⟨x,y,hx,hy,pair⟩⟩

end PalomarI3380.SquareRepresentation.SetContext
