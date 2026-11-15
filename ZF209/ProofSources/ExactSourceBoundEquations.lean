module
public import ExactSourceBoundModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma bound_same_node_iff (t x y a b : M) (ht : t<8) :
 modelSourceNode t x y=modelSourceNode t a b ↔ x=a ∧ y=b := by
 constructor
 · intro h; have hi := modelSourceNode_injective t x y t a b ht ht h; exact hi.2
 · rintro ⟨rfl,rfl⟩; rfl

lemma modelShiftIndex_fixed (k i : M) :
 graphValue shiftIndexGraph shiftIndexGraph_total ![k,i]=i ↔ i<k := by
 calc
  _ ↔ i=graphValue shiftIndexGraph shiftIndexGraph_total ![k,i] := eq_comm
  _ ↔ shiftIndexGraph.val.Evalb ![i,k,i] := (graphValue_spec shiftIndexGraph shiftIndexGraph_total i ![k,i]).symm
  _ ↔ i<k := by simp [shiftIndexGraph,ne_of_lt (lt_add_one i)]

lemma modelSourceBound_atomic (k t a b : M) (hat : t=1 ∨ t=2) :
 modelSourceBound k (modelSourceNode t a b) ↔ a<k ∧ b<k := by
 have ht : t<8 := by
  rcases hat with h|h
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (1:Nat)<8 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (2:Nat)<8 by decide))
 have hp : 0<t := by rcases hat with h|h <;> rw [h] <;> simp
 have hn := modelSourceNode_pos_of_tag t a b hp
 unfold modelSourceBound
 rw [modelSourceWf_node t a b ht hn,modelSourceShift_atomic k t a b hat,
  bound_same_node_iff _ _ _ _ _ ht,modelShiftIndex_fixed,modelShiftIndex_fixed]
 rcases hat with h|h <;> subst t <;> simp

lemma modelSourceBound_binary (k t a b : M) (hbt : t=3 ∨ t=4 ∨ t=5) :
 modelSourceBound k (modelSourceNode t a b) ↔ modelSourceBound k a ∧ modelSourceBound k b := by
 have ht : t<8 := by
  rcases hbt with h|h|h
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (3:Nat)<8 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (4:Nat)<8 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (5:Nat)<8 by decide))
 have hp : 0<t := by
  rcases hbt with h|h|h
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<3 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<4 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<5 by decide))
 have hn := modelSourceNode_pos_of_tag t a b hp
 unfold modelSourceBound
 rw [modelSourceWf_node t a b ht hn,modelSourceShift_binary k t a b hbt,
  bound_same_node_iff _ _ _ _ _ ht]
 rcases hbt with h|h|h <;> subst t <;> simp [and_assoc,and_left_comm,and_comm]

lemma modelSourceBound_binder (k t a : M) (hqt : t=6 ∨ t=7) :
 modelSourceBound k (modelSourceNode t a 0) ↔ modelSourceBound (k+1) a := by
 have ht : t<8 := by
  rcases hqt with h|h
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (6:Nat)<8 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (7:Nat)<8 by decide))
 have hp : 0<t := by
  rcases hqt with h|h
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<6 by decide))
  · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<7 by decide))
 have hn := modelSourceNode_pos_of_tag t a 0 hp
 unfold modelSourceBound
 rw [modelSourceWf_node t a 0 ht hn,modelSourceShift_binder k t a hqt,
  bound_same_node_iff _ _ _ _ _ ht]
 rcases hqt with h|h <;> subst t <;> simp

lemma modelSourceBound_node (k t a b : M) (ht : t<8) (hn : 0<modelSourceNode t a b) :
 modelSourceBound k (modelSourceNode t a b) ↔
 ((t=1 ∨ t=2) ∧ a<k ∧ b<k) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ modelSourceBound k a ∧ modelSourceBound k b) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ modelSourceBound (k+1) a) := by
 by_cases hat : t=1 ∨ t=2
 · rw [modelSourceBound_atomic k t a b hat]
   rcases hat with h|h <;> subst t <;> simp
 by_cases hbt : t=3 ∨ t=4 ∨ t=5
 · rw [modelSourceBound_binary k t a b hbt]
   rcases hbt with h|h|h <;> subst t <;> simp
 by_cases hqt : (t=6 ∨ t=7) ∧ b=0
 · obtain ⟨hqt,rfl⟩ := hqt
   rw [modelSourceBound_binder k t a hqt]
   rcases hqt with h|h <;> subst t <;> simp
 constructor
 · intro h
   have hw := (modelSourceWf_node t a b ht hn).mp h.1
   rcases hw with h|⟨h,_,_⟩|⟨h,hb,_⟩
   · exact False.elim (hat h)
   · exact False.elim (hbt h)
   · exact False.elim (hqt ⟨h,hb⟩)
 · intro h
   rcases h with ⟨h,_,_⟩|⟨h,_,_⟩|⟨h,hb,_⟩
   · exact False.elim (hat h)
   · exact False.elim (hbt h)
   · exact False.elim (hqt ⟨h,hb⟩)

end ZFR.ArithmeticRepresentation
