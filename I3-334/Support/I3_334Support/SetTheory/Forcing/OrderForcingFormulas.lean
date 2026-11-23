module
public import I3_334Support.SetTheory.Rank.RankOrderClosure
public import I3_334Support.SetTheory.ClassModel
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem endExtends_def {n a s r b t f : Nat}
    (ha : a < n) (hs : s < n) (hr : r < n) (hb : b < n) (ht : t < n) (hf : f < n) :
    N.square.Definable n (fun v => N.EndExtends (v a) (v s) (v r) (v b) (v t) (v f)) := by
  have left := Definable.graphValue (N := N) (n := n + 2) (i := r + 2) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have right := Definable.graphValue (N := N) (n := n + 2) (i := f + 2) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have borrowed := Definable.boundedAll hs _ (Definable.boundedAll (i := s + 1) (by omega) _ (left.iff right))
  have fresh := (Definable.mem (N := N) (n := n + 2) (i := 0) (j := s + 2) (by omega) (by omega)).not
  have initial := Definable.boundedAll hs _ (Definable.boundedAll (i := t + 1) (by omega) _ (fresh.implies right))
  exact ((Definable.subset ha hb).and (borrowed.and initial)).congr fun _ =>
    ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩, fun h => ⟨h.height,h.agrees,h.initial⟩⟩

theorem refines_def {n p q : Nat} (hp : p < n) (hq : q < n) :
    N.square.Definable n (fun v => N.Refines (v p) (v q)) := by
  have weak := N.rankOrder_def (n := n + 6) (p := q + 6) (a := 5) (s := 4) (r := 3)
    (by omega) (by omega) (by omega) (by omega)
  have strong := N.rankOrder_def (n := n + 6) (p := p + 6) (a := 2) (s := 1) (r := 0)
    (by omega) (by omega) (by omega) (by omega)
  have rel := N.endExtends_def (n := n + 6) (a := 5) (s := 4) (r := 3) (b := 2) (t := 1) (f := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (Definable.ex
    (Definable.ex (Definable.ex (Definable.ex (weak.and (strong.and rel)))))))

def OrderEdge (code x y : V) : Prop :=
  ∃ a stage rel, N.RankOrder code a stage rel ∧ N.mem x stage ∧ N.mem y stage ∧
    Internal.At N.mem rel x y

def Covers (p x : V) : Prop :=
  ∃ a stage graph, N.RankOrder p a stage graph ∧ N.mem x stage

theorem orderEdge_def {n p x y : Nat} (hp : p < n) (hx : x < n) (hy : y < n) :
    N.square.Definable n (fun v => N.OrderEdge (v p) (v x) (v y)) := by
  have condition := N.rankOrder_def (n := n + 3) (p := p + 3) (a := 2) (s := 1) (r := 0)
    (by omega) (by omega) (by omega) (by omega)
  have left := Definable.mem (N := N) (n := n + 3) (i := x + 3) (j := 1) (by omega) (by omega)
  have right := Definable.mem (N := N) (n := n + 3) (i := y + 3) (j := 1) (by omega) (by omega)
  have graph := Definable.graphValue (N := N) (n := n + 3) (i := 0) (j := x + 3) (k := y + 3)
    (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (Definable.ex (condition.and (left.and (right.and graph)))))

theorem covers_def {n p x : Nat} (hp : p < n) (hx : x < n) :
    N.square.Definable n (fun v => N.Covers (v p) (v x)) :=
  Definable.ex (Definable.ex (Definable.ex
    ((N.rankOrder_def (n := n + 3) (p := p + 3) (a := 2) (s := 1) (r := 0)
      (by omega) (by omega) (by omega) (by omega)).and
      (Definable.mem (N := N) (n := n + 3) (i := x + 3) (j := 1) (by omega) (by omega)))))

theorem covers_larger {p q x : V} (h : N.Refines q p) (member : N.Covers p x) : N.Covers q x := by
  obtain ⟨a,s,r,cond,inside⟩ := member
  obtain ⟨d,b,f,height,t,g,c₀,c₁,ex⟩ := h
  obtain ⟨ha,hs,hr⟩ := N.rankOrder_unique cond c₀
  subst d
  subst b
  subst f
  exact ⟨height,t,g,c₁,N.rank_subset cond.ranked c₁.ranked ex.height x inside⟩

theorem orderEdge_larger {p q x y : V} (h : N.Refines q p) (edge : N.OrderEdge p x y) :
    N.OrderEdge q x y := by
  obtain ⟨a,s,r,cond,hx,hy,out⟩ := edge
  obtain ⟨d,b,f,height,t,g,c₀,c₁,ex⟩ := h
  obtain ⟨ha,hs,hr⟩ := N.rankOrder_unique cond c₀
  subst d
  subst b
  subst f
  have sub := N.rank_subset cond.ranked c₁.ranked ex.height
  exact ⟨height,t,g,c₁,sub x hx,sub y hy,(ex.agrees x hx y hy).mp out⟩

theorem orderEdge_at {p a s r x y : V} (h : N.RankOrder p a s r) (hx : N.mem x s) (hy : N.mem y s) :
    N.OrderEdge p x y ↔ Internal.At N.mem r x y := by
  constructor
  · rintro ⟨b,t,f,new,_,_,proof⟩
    have eq := (N.rankOrder_unique new h).2.2
    exact eq ▸ proof
  · exact fun edge => ⟨a,s,r,h,hx,hy,edge⟩

theorem orders_cover {w p : V} (omega : Internal.Omega N.mem w) (foundation : N.Regular)
    (condition : N.OrderCondition p) (x : V) :
    ∃ q, N.Refines q p ∧ N.Covers q x := by
  obtain ⟨a,s,r,h⟩ := condition
  obtain ⟨b,t,ranked,member⟩ := N.rank_cover omega foundation x
  rcases N.ordinal_compare h.ranked.1 ranked.1 with smaller | same | bigger
  · obtain ⟨q,g,cond,reach⟩ := N.extend_rankOrder h ranked (ranked.1.transitive a smaller)
    exact ⟨q,reach,b,t,g,cond,member⟩
  · subst b
    have same : t = s := N.rank_unique ranked h.ranked
    exact ⟨p,N.refines_refl ⟨a,s,r,h⟩,a,s,r,h,same ▸ member⟩
  · exact ⟨p,N.refines_refl ⟨a,s,r,h⟩,a,s,r,h, N.rank_subset ranked h.ranked (h.ranked.1.transitive b bigger) x member⟩

end PalomarI3380.SquareRepresentation.SetContext
