module
public import ExactSourceSubstModel
public import ModelNumeralOrder
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelSourceSubst_branch (d r n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n]) :
 (substTransformBranchGraph substIndexGraph).val.Evalb
 ![modelSourceSubst d r n, (sourceSubstHistory (M := M)).result ![r] (modelCantor d n),d,n,t,a,b,r] := by
 have he := modelSourceSubst_step d r n
 unfold modelSubstTransformStep at he
 have hd : graphValue unpairLeftGraph unpairLeftGraph_total ![modelCantor d n]=d := modelUnpairLeft_pair d n
 have hn : graphValue unpairRightGraph unpairRightGraph_total ![modelCantor d n]=n := modelUnpairRight_pair d n
 rw [hd,hn] at he
 dsimp only at he
 have ht' := (graphValue_spec radix8ResidueGraph radix8ResidueGraph_total t ![n]).mp ht
 have ha' := (graphValue_spec sourceLeftGraph sourceLeftGraph_total a ![n]).mp ha
 have hb' := (graphValue_spec sourceRightGraph sourceRightGraph_total b ![n]).mp hb
 rw [←ht',←ha',←hb'] at he
 exact (graphValue_spec (substTransformBranchGraph substIndexGraph)
   (substTransformBranchGraph_total substIndexGraph substIndexGraph_total) _ _).mpr he

lemma modelSourceSubst_zero (d r : M) : modelSourceSubst d r 0=0 := by
 obtain ⟨t,ht,_⟩ := radix8ResidueGraph_total (M := M) ![0]
 obtain ⟨a,ha,_⟩ := sourceLeftGraph_total (M := M) ![0]
 obtain ⟨b,hb,_⟩ := sourceRightGraph_total (M := M) ![0]
 have h := (substTransformBranchGraph_eval substIndexGraph substIndexGraph_total _ _ _ _ _ _ _ _).mp
   (modelSourceSubst_branch d r 0 t a b ht ha hb)
 simpa using h

lemma modelSourceSubst_node_branch (d r t a b : M) (ht : t<8) :
 (substTransformBranchGraph substIndexGraph).val.Evalb
 ![modelSourceSubst d r (modelSourceNode t a b),
 (sourceSubstHistory (M := M)).result ![r] (modelCantor d (modelSourceNode t a b)),
 d,modelSourceNode t a b,t,a,b,r] := by
 obtain ⟨ht,ha,hb⟩ := source_decoder_node t a b ht
 exact modelSourceSubst_branch d r _ _ _ _ ht ha hb

lemma modelSubstSourceNode_pos_of_tag (t a b : M) (ht : 0<t) : 0<modelSourceNode t a b :=
 lt_of_lt_of_le ht (by simp [modelSourceNode])

lemma modelSourceSubst_binary_left (d r t a b : M) (hn : 0<modelSourceNode t a b) :
 znth ((sourceSubstHistory (M := M)).result ![r] (modelCantor d (modelSourceNode t a b)))
  (modelCantor d a)=modelSourceSubst d r a := by
 apply modelSourceSubst_lookup
 apply modelCantor_sum_lt
 simpa only [add_comm] using (_root_.add_lt_add_left (modelSourceNode_left_lt t a b hn) d)

lemma modelSourceSubst_binary_right (d r t a b : M) (hn : 0<modelSourceNode t a b) :
 znth ((sourceSubstHistory (M := M)).result ![r] (modelCantor d (modelSourceNode t a b)))
  (modelCantor d b)=modelSourceSubst d r b := by
 apply modelSourceSubst_lookup
 apply modelCantor_sum_lt
 simpa only [add_comm] using (_root_.add_lt_add_left (modelSourceNode_right_lt t a b hn) d)

lemma modelSourceSubst_binary (d r t a b : M) (ht : t=3 ∨ t=4 ∨ t=5) :
 modelSourceSubst d r (modelSourceNode t a b)=modelSourceNode t (modelSourceSubst d r a) (modelSourceSubst d r b) := by
 have hp : 0<t := by
   rcases ht with h|h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<3 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<4 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<5 by decide))
 have hb : t<8 := by
   rcases ht with h|h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (3:Nat)<8 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (4:Nat)<8 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (5:Nat)<8 by decide))
 have hn := modelSubstSourceNode_pos_of_tag t a b hp
 have h := (substTransformBranchGraph_eval substIndexGraph substIndexGraph_total _ _ _ _ _ _ _ _).mp
   (modelSourceSubst_node_branch d r t a b hb)
 rw [modelSourceSubst_binary_left d r t a b hn,modelSourceSubst_binary_right d r t a b hn] at h
 rcases ht with htag|htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h

lemma modelSourceSubst_atomic (d r t a b : M) (ht : t=1 ∨ t=2) :
 modelSourceSubst d r (modelSourceNode t a b)=modelSourceNode t
   (graphValue substIndexGraph substIndexGraph_total ![d,r,a])
   (graphValue substIndexGraph substIndexGraph_total ![d,r,b]) := by
 have hp : 0<t := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<1 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<2 by decide))
 have hb : t<8 := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (1:Nat)<8 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (2:Nat)<8 by decide))
 have hn := modelSubstSourceNode_pos_of_tag t a b hp
 have h := (substTransformBranchGraph_eval substIndexGraph substIndexGraph_total _ _ _ _ _ _ _ _).mp
   (modelSourceSubst_node_branch d r t a b hb)
 rcases ht with htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h

lemma modelSourceSubst_binder (d r t a : M) (ht : t=6 ∨ t=7) :
 modelSourceSubst d r (modelSourceNode t a 0)=modelSourceNode t (modelSourceSubst (d+1) r a) 0 := by
 have hp : 0<t := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<6 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<7 by decide))
 have hb : t<8 := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (6:Nat)<8 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (7:Nat)<8 by decide))
 have hgt : 1<t := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (1:Nat)<6 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (1:Nat)<7 by decide))
 have hn := modelSubstSourceNode_pos_of_tag t a 0 hp
 have h := (substTransformBranchGraph_eval substIndexGraph substIndexGraph_total _ _ _ _ _ _ _ _).mp
   (modelSourceSubst_node_branch d r t a 0 hb)
 rw [modelSourceSubst_lookup (d+1) r a _ (modelBinderIndex_descent d t a hgt)] at h
 rcases ht with htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h


lemma modelSourceSubst_malformed (d r n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n])
 (hbad : ¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0))) :
 modelSourceSubst d r n=0 := by
 have h := (substTransformBranchGraph_eval substIndexGraph substIndexGraph_total _ _ _ _ _ _ _ _).mp
   (modelSourceSubst_branch d r n t a b ht ha hb)
 rcases h with ⟨_,hz⟩|⟨_,h⟩
 · exact hz
 rcases h with ⟨h,_⟩|⟨h,_⟩|⟨h,hb,_⟩|⟨_,hz⟩
 · exfalso; apply hbad; rcases h with h|h
   · exact Or.inl h
   · exact Or.inr (Or.inl h)
 · exfalso; apply hbad; rcases h with h|h|h
   · exact Or.inr (Or.inr (Or.inl h))
   · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
   · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
 · exact False.elim (hbad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h,hb⟩))))))
 · exact hz

end ZFR.ArithmeticRepresentation
