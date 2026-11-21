module
public import I3_380.RankOrderExtension
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

private theorem order_parts (source : V) :
    ∃ heights graphs,
      (∀ a, N.mem a heights ↔ ∃ code, N.mem code source ∧ ∃ r, Internal.OrderedPair N.mem a r code) ∧
      (∀ r, N.mem r graphs ↔ ∃ code, N.mem code source ∧ ∃ a, Internal.OrderedPair N.mem a r code) := by
  have first := Definable.ex (Definable.orderedPair (N := N) (n := 3) (i := 2) (j := 0) (k := 1)
    (by decide) (by decide) (by decide))
  have second := Definable.ex (Definable.orderedPair (N := N) (n := 3) (i := 0) (j := 2) (k := 1)
    (by decide) (by decide) (by decide))
  obtain ⟨heights, stored⟩ := N.image [] first (fun _ _ _ ⟨_,a⟩ ⟨_,b⟩ => (Internal.orderedPair_injective a b).1) source
  obtain ⟨graphs, found⟩ := N.image [] second (fun _ _ _ ⟨_,a⟩ ⟨_,b⟩ => (Internal.orderedPair_injective a b).2) source
  exact ⟨heights,graphs,stored,found⟩

private theorem index_parts {source heights graphs : V}
    (valid : ∀ code, N.mem code source → N.OrderCondition code)
    (hHeights : ∀ a, N.mem a heights ↔ ∃ code, N.mem code source ∧ ∃ r, Internal.OrderedPair N.mem a r code)
    (hGraphs : ∀ r, N.mem r graphs ↔ ∃ code, N.mem code source ∧ ∃ a, Internal.OrderedPair N.mem a r code) :
    (∀ a, N.mem a heights ↔ ∃ p s r, N.mem p source ∧ N.RankOrder p a s r) ∧
    (∀ r, N.mem r graphs ↔ ∃ p a s, N.mem p source ∧ N.RankOrder p a s r) := by
  constructor
  · intro a
    refine (hHeights a).trans ⟨?_, fun ⟨p,s,r,hp,h⟩ => ⟨p,hp,r,h.encoding⟩⟩
    rintro ⟨p,hp,r,pair⟩
    obtain ⟨b,s,t,h⟩ := valid p hp
    obtain ⟨same,_⟩ := Internal.orderedPair_injective h.encoding pair
    subst b
    exact ⟨p,s,t,hp,h⟩
  · intro r
    refine (hGraphs r).trans ⟨?_, fun ⟨p,a,s,hp,h⟩ => ⟨p,hp,a,h.encoding⟩⟩
    rintro ⟨p,hp,a,pair⟩
    obtain ⟨b,s,t,h⟩ := valid p hp
    obtain ⟨_,same⟩ := Internal.orderedPair_injective h.encoding pair
    subst t
    exact ⟨p,b,s,hp,h⟩

theorem refines_transport {p q a s r b t g : V}
    (hs : N.RankOrder p a s r) (ht : N.RankOrder q b t g) (h : N.Refines q p) :
    N.EndExtends a s r b t g := by
  obtain ⟨a',s',r',b',t',g',first,next,ex⟩ := h
  obtain ⟨ha,hs,hr⟩ := N.rankOrder_unique hs first
  obtain ⟨hb,ht,hg⟩ := N.rankOrder_unique ht next
  subst a'
  subst s'
  subst r'
  subst b'
  subst t'
  subst g'
  exact ex

theorem empty_rankOrder : ∃ p, N.OrderCondition p := by
  obtain ⟨stage,rank⟩ := N.rank_exists N.ordinal_empty
  obtain ⟨p,r,h⟩ := N.any_rankOrder rank
  exact ⟨p,N.empty,stage,r,h⟩

/-- A model-internal set of mutually end-extending conditions has a
common extension. Its domain is the rank at the supremum of the heights. -/
theorem close_order_conditions (conditions : V)
    (valid : ∀ p, N.mem p conditions → N.OrderCondition p)
    (chain : ∀ p q, N.mem p conditions → N.mem q conditions → N.Refines p q ∨ N.Refines q p) :
    ∃ code height stage graph, N.RankOrder code height stage graph ∧
      ∀ p, N.mem p conditions → N.Refines code p := by
  obtain ⟨heights,graphs,hA,hR⟩ := N.order_parts conditions
  obtain ⟨containsHeight,containsGraph⟩ := N.index_parts valid hA hR
  let height := N.union heights
  let graph := N.union graphs
  have ordinal : N.Ordinal height := N.ordinal_union heights fun a ha => by
    obtain ⟨p,s,r,hp,cond⟩ := (containsHeight a).mp ha
    exact cond.ranked.1
  obtain ⟨stage,rank⟩ := N.rank_exists ordinal
  have upper {p a s r : V} (hp : N.mem p conditions) (h : N.RankOrder p a s r) : N.Subset a height :=
    fun x hx => (N.mem_union _ _).mpr ⟨a,(containsHeight a).mpr ⟨p,s,r,hp,h⟩,hx⟩
  have fits {p a s r : V} (hp : N.mem p conditions) (h : N.RankOrder p a s r) : N.Subset s stage :=
    N.rank_subset h.ranked rank (upper hp h)
  have cofinal (x : V) (hx : N.mem x stage) :
      ∃ p a s r, N.mem p conditions ∧ N.RankOrder p a s r ∧ N.mem x s := by
    obtain ⟨α,b,inside,rankB,hs⟩ := (N.mem_rank_iff rank x).mp hx
    obtain ⟨β,seen,ancestor⟩ := (N.mem_union heights α).mp inside
    obtain ⟨p,s,r,member,cond⟩ := (containsHeight β).mp seen
    exact ⟨p,β,s,r,member,cond,(N.mem_rank_iff cond.ranked x).mpr ⟨α,b,ancestor,rankB,hs⟩⟩
  have relation {x y : V} : Internal.At N.mem graph x y ↔
      ∃ p a s r, N.mem p conditions ∧ N.RankOrder p a s r ∧ Internal.At N.mem r x y := by
    simp only [N.at_pair,graph,N.mem_union,containsGraph]
    constructor
    · rintro ⟨r,⟨p,a,s,hp,cond⟩,edge⟩
      exact ⟨p,a,s,r,hp,cond,edge⟩
    · rintro ⟨p,a,s,r,hp,cond,edge⟩
      exact ⟨r,⟨p,a,s,hp,cond⟩,edge⟩
  have typed {p a s r x y : V} (h : N.RankOrder p a s r) (edge : Internal.At N.mem r x y) :
      N.mem x s ∧ N.mem y s := by
    obtain ⟨c,hc,pair⟩ := edge
    obtain ⟨u,v,hu,hv,code⟩ := h.shaped c hc
    obtain ⟨same,eq⟩ := Internal.orderedPair_injective code pair
    exact ⟨same ▸ hu,eq ▸ hv⟩
  have restriction {p a s r : V} (hp : N.mem p conditions) (cond : N.RankOrder p a s r) :
      N.EndExtends a s r height stage graph := by
    refine ⟨upper hp cond,fun x hx y hy => ⟨fun h => relation.mpr ⟨p,a,s,r,hp,cond,h⟩,?_⟩,?_⟩
    · intro edge
      obtain ⟨q,β,t,g,hq,other,out⟩ := relation.mp edge
      rcases chain q p hq hp with ex | ex
      · exact ((N.refines_transport cond other ex).agrees x hx y hy).mpr out
      · obtain ⟨xIn,yIn⟩ := typed other out
        exact ((N.refines_transport other cond ex).agrees x xIn y yIn).mp out
    · intro x hx y hy notIn
      obtain ⟨q,β,t,g,hq,other,yIn⟩ := cofinal y hy
      rcases chain q p hq hp with ex | ex
      · exact relation.mpr ⟨q,β,t,g,hq,other,(N.refines_transport cond other ex).initial x hx y yIn notIn⟩
      · exact (notIn (N.rank_subset other.ranked cond.ranked (N.refines_transport other cond ex).height y yIn)).elim
  have jointly {p q a b s t r g : V} (hp : N.mem p conditions) (hq : N.mem q conditions)
      (first : N.RankOrder p a s r) (second : N.RankOrder q b t g) :
      ∃ k β u f, N.mem k conditions ∧ N.RankOrder k β u f ∧ N.Subset s u ∧ N.Subset t u := by
    rcases chain p q hp hq with ex | ex
    · exact ⟨p,a,s,r,hp,first,N.subset_refl _,N.rank_subset second.ranked first.ranked (N.refines_transport second first ex).height⟩
    · exact ⟨q,b,t,g,hq,second,N.rank_subset first.ranked second.ranked (N.refines_transport first second ex).height,N.subset_refl _⟩
  have order : N.WellOrderOn (Internal.At N.mem graph) stage := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx edge
      obtain ⟨p,a,s,r,hp,cond,inside⟩ := cofinal x hx
      exact cond.order.irrefl x inside (((restriction hp cond).agrees x inside x inside).mpr edge)
    · intro x y z hx hy hz xy yz
      obtain ⟨p,a,s,r,hp,first,xIn⟩ := cofinal x hx
      obtain ⟨q,b,t,g,hq,second,yIn⟩ := cofinal y hy
      obtain ⟨i,c,u,f,hi,pair,left,right⟩ := jointly hp hq first second
      obtain ⟨j,d,v,h,hj,third,zIn⟩ := cofinal z hz
      obtain ⟨k,e,w,rel,hk,all,init,last⟩ := jointly hi hj pair third
      have xW := init x (left x xIn)
      have yW := init y (right y yIn)
      have zW := last z zIn
      have incl := restriction hk all
      exact (incl.agrees x xW z zW).mp (all.order.trans x y z xW yW zW
        ((incl.agrees x xW y yW).mpr xy) ((incl.agrees y yW z zW).mpr yz))
    · intro x y hx hy
      obtain ⟨p,a,s,r,hp,first,xIn⟩ := cofinal x hx
      obtain ⟨q,b,t,g,hq,second,yIn⟩ := cofinal y hy
      obtain ⟨i,c,u,f,hi,cond,left,right⟩ := jointly hp hq first second
      have xU := left x xIn
      have yU := right y yIn
      have incl := restriction hi cond
      exact (or_congr (incl.agrees x xU y yU) (or_congr Iff.rfl (incl.agrees y yU x xU))).mp
        (cond.order.compare x y xU yU)
    · intro a sub has
      obtain ⟨x, hx⟩ := has
      obtain ⟨p,h,s,r,hp,cond,xIn⟩ := cofinal x (sub x hx)
      let cut := N.inter a s
      have contained : N.Subset cut s := fun z hz => ((N.mem_inter _ _ _).mp hz).2
      obtain ⟨z, hz, smallest⟩ := cond.order.least cut contained
        ⟨x,(N.mem_inter _ _ _).mpr ⟨hx,xIn⟩⟩
      obtain ⟨inA,inStage⟩ := (N.mem_inter _ _ _).mp hz
      have incl := restriction hp cond
      refine ⟨z,inA,fun y hy => ?_⟩
      classical
      by_cases hyS : N.mem y s
      · exact (smallest y ((N.mem_inter _ _ _).mpr ⟨hy,hyS⟩)).elim Or.inl
          (fun h => Or.inr ((incl.agrees z inStage y hyS).mp h))
      · exact Or.inr (incl.initial z inStage y (sub y hy) hyS)
  have shape : N.RelationOn graph stage := by
    intro pair hp
    obtain ⟨f, inGraph, member⟩ := (N.mem_union _ _).mp hp
    obtain ⟨p,a,s,hp,cond⟩ := (containsGraph f).mp inGraph
    obtain ⟨x,y,hx,hy,code⟩ := cond.shaped pair member
    exact ⟨x,y,fits hp cond x hx,fits hp cond y hy,code⟩
  let code := N.orderedPair height graph
  have condition : N.RankOrder code height stage graph :=
    ⟨N.orderedPair_intro _ _,rank,order,shape⟩
  exact ⟨code,height,stage,graph,condition,fun p hp => by
    obtain ⟨a,s,r,h⟩ := valid p hp
    exact ⟨a,s,r,height,stage,graph,h,condition,restriction hp h⟩⟩

end PalomarI3380.SquareRepresentation.SetContext
