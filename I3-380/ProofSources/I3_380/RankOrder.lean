module
public import I3_380.BinaryGraphs
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic
variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

def RelationOn (graph domain : V) : Prop :=
  ∀ p, N.mem p graph → ∃ x y, N.mem x domain ∧ N.mem y domain ∧ Internal.OrderedPair N.mem x y p

theorem relationOn_def {n f d : Nat} (hf : f < n) (hd : d < n) :
    N.square.Definable n (fun env => N.RelationOn (env f) (env d)) := by
  have source := Definable.mem (N := N) (n := n + 3) (i := 1) (j := d + 3) (by omega) (by omega)
  have target := Definable.mem (N := N) (n := n + 3) (i := 0) (j := d + 3) (by omega) (by omega)
  have pair := Definable.orderedPair (N := N) (n := n + 3) (i := 1) (j := 0) (k := 2)
    (by omega) (by omega) (by omega)
  exact Definable.boundedAll hf _ (Definable.ex (Definable.ex (source.and (target.and pair))))

/-- A condition names a wellorder of a set rank. Its code consists of the
height and the graph. The domain is recovered uniquely from the height. -/
structure RankOrder (code height stage graph : V) : Prop where
  encoding : Internal.OrderedPair N.mem height graph code
  ranked : N.Rank height stage
  order : N.WellOrderOn (Internal.At N.mem graph) stage
  shaped : N.RelationOn graph stage

def OrderCondition (code : V) : Prop := ∃ a s r, N.RankOrder code a s r

theorem rankOrder_def {n p a s r : Nat} (hp : p < n) (ha : a < n) (hs : s < n) (hr : r < n) :
    N.square.Definable n (fun env => N.RankOrder (env p) (env a) (env s) (env r)) := by
  have key := Definable.orderedPair (N := N) ha hr hp
  have rank := Definable.rank (N := N) ha hs
  have relation := Definable.wellOrder (N := N) (R := Internal.At N.mem)
    (Definable.graph_relation (N := N)) hr hs
  have shape := N.relationOn_def hr hs
  exact (key.and (rank.and (relation.and shape))).congr fun _ =>
    ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.encoding,h.ranked,h.order,h.shaped⟩⟩

theorem orderCondition_def {n p : Nat} (hp : p < n) :
    N.square.Definable n (fun env => N.OrderCondition (env p)) :=
  Definable.ex (Definable.ex (Definable.ex (N.rankOrder_def
    (n := n + 3) (p := p + 3) (a := 2) (s := 1) (r := 0)
    (by omega) (by omega) (by omega) (by omega))))

theorem rankOrder_unique {p a b s t r q : V} (first : N.RankOrder p a s r) (second : N.RankOrder p b t q) :
    a = b ∧ s = t ∧ r = q := by
  obtain ⟨same, eq⟩ := Internal.orderedPair_injective first.encoding second.encoding
  subst b
  exact ⟨rfl,N.rank_unique first.ranked second.ranked,eq⟩

structure EndExtends (low dom previous high range next : V) : Prop where
  height : N.Subset low high
  agrees : ∀ x, N.mem x dom → ∀ y, N.mem y dom →
    (Internal.At N.mem previous x y ↔ Internal.At N.mem next x y)
  initial : ∀ x, N.mem x dom → ∀ y, N.mem y range → ¬ N.mem y dom →
    Internal.At N.mem next x y

theorem extension_refl (height stage graph : V) : N.EndExtends height stage graph height stage graph :=
  ⟨N.subset_refl _,fun _ _ _ _ => Iff.rfl,fun _ _ _ hy no => (no hy).elim⟩

theorem extension_trans {a b c x y z f g h : V}
    (xa : N.Rank a x) (yb : N.Rank b y)
    (first : N.EndExtends a x f b y g) (second : N.EndExtends b y g c z h) :
    N.EndExtends a x f c z h := by
  have sub := N.rank_subset xa yb first.height
  refine ⟨N.subset_trans first.height second.height,fun u hu v hv =>
    (first.agrees u hu v hv).trans (second.agrees u (sub u hu) v (sub v hv)),?_⟩
  intro u hu v hv removed
  classical
  by_cases previous : N.mem v y
  · exact (second.agrees u (sub u hu) v previous).mp (first.initial u hu v previous removed)
  · exact second.initial u (sub u hu) v hv previous

def Refines (strong weak : V) : Prop :=
  ∃ a x f b y g, N.RankOrder weak a x f ∧ N.RankOrder strong b y g ∧ N.EndExtends a x f b y g

theorem refines_refl {p : V} (cond : N.OrderCondition p) : N.Refines p p := by
  obtain ⟨a,s,r,h⟩ := cond
  exact ⟨a,s,r,a,s,r,h,h,N.extension_refl _ _ _⟩

theorem refines_trans {p q r : V} (pq : N.Refines p q) (qr : N.Refines q r) : N.Refines p r := by
  obtain ⟨a,x,f,b,y,g,atQ,atP,ex⟩ := pq
  obtain ⟨c,z,h,a',x',f',atR,atQ',ex'⟩ := qr
  obtain ⟨sameA, sameX, sameF⟩ := N.rankOrder_unique atQ atQ'
  subst a'
  subst x'
  subst f'
  exact ⟨c,z,h,b,y,g,atR,atP,N.extension_trans atR.ranked atQ.ranked ex' ex⟩

theorem refines_strong {p q : V} (h : N.Refines p q) : N.OrderCondition p := by
  obtain ⟨a,s,r,b,t,g,weak,strong,extends_⟩ := h
  exact ⟨b,t,g,strong⟩

theorem refines_weak {p q : V} (h : N.Refines p q) : N.OrderCondition q := by
  obtain ⟨a,s,r,b,t,g,weak,strong,extends_⟩ := h
  exact ⟨a,s,r,weak⟩


end SetContext
end PalomarI3380.SquareRepresentation
