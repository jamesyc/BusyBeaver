module
public import GenericSourceTransformModel
public import ModelNumeralOrder
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation.GenericTransform
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (idx : 𝚺ᴬ₁.Semisentence 3) (hi : GraphTotalIn (M:=M) idx)

lemma modelTransform_branch (d n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n]) :
 (transformBranchGraph idx).val.Evalb
 ![modelTransform idx hi d n, (transformHistory idx hi).result ![] (modelCantor d n),d,n,t,a,b] := by
 have he := modelTransform_step idx hi d n
 unfold modelTransformStep at he
 have hd : graphValue unpairLeftGraph unpairLeftGraph_total ![modelCantor d n]=d := modelUnpairLeft_pair d n
 have hn : graphValue unpairRightGraph unpairRightGraph_total ![modelCantor d n]=n := modelUnpairRight_pair d n
 rw [hd,hn] at he
 dsimp only at he
 have ht' := (graphValue_spec radix8ResidueGraph radix8ResidueGraph_total t ![n]).mp ht
 have ha' := (graphValue_spec sourceLeftGraph sourceLeftGraph_total a ![n]).mp ha
 have hb' := (graphValue_spec sourceRightGraph sourceRightGraph_total b ![n]).mp hb
 rw [←ht',←ha',←hb'] at he
 exact (graphValue_spec (transformBranchGraph idx)
   (transformBranchGraph_total idx hi) _ _).mpr he

lemma modelTransform_zero (d : M) : modelTransform idx hi d 0=0 := by
 obtain ⟨t,ht,_⟩ := radix8ResidueGraph_total (M := M) ![0]
 obtain ⟨a,ha,_⟩ := sourceLeftGraph_total (M := M) ![0]
 obtain ⟨b,hb,_⟩ := sourceRightGraph_total (M := M) ![0]
 have h := (transformBranchGraph_eval idx hi _ _ _ _ _ _ _).mp
   (modelTransform_branch idx hi d 0 t a b ht ha hb)
 simpa using h

lemma modelTransform_node_branch (d t a b : M) (ht : t<8) :
 (transformBranchGraph idx).val.Evalb
 ![modelTransform idx hi d (modelSourceNode t a b),
 (transformHistory idx hi).result ![] (modelCantor d (modelSourceNode t a b)),
 d,modelSourceNode t a b,t,a,b] := by
 obtain ⟨ht,ha,hb⟩ := source_decoder_node t a b ht
 exact modelTransform_branch idx hi d _ _ _ _ ht ha hb

lemma modelSourceNode_pos_of_tag (t a b : M) (ht : 0<t) : 0<modelSourceNode t a b :=
 lt_of_lt_of_le ht (by simp [modelSourceNode])

lemma modelTransform_binary_left (d t a b : M) (hn : 0<modelSourceNode t a b) :
 znth ((transformHistory idx hi).result ![] (modelCantor d (modelSourceNode t a b)))
  (modelCantor d a)=modelTransform idx hi d a := by
 apply modelTransform_lookup idx hi
 apply modelCantor_sum_lt
 simpa only [add_comm] using (_root_.add_lt_add_left (modelSourceNode_left_lt t a b hn) d)

lemma modelTransform_binary_right (d t a b : M) (hn : 0<modelSourceNode t a b) :
 znth ((transformHistory idx hi).result ![] (modelCantor d (modelSourceNode t a b)))
  (modelCantor d b)=modelTransform idx hi d b := by
 apply modelTransform_lookup idx hi
 apply modelCantor_sum_lt
 simpa only [add_comm] using (_root_.add_lt_add_left (modelSourceNode_right_lt t a b hn) d)

lemma modelTransform_binary (d t a b : M) (ht : t=3 ∨ t=4 ∨ t=5) :
 modelTransform idx hi d (modelSourceNode t a b)=modelSourceNode t (modelTransform idx hi d a) (modelTransform idx hi d b) := by
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
 have hn := modelSourceNode_pos_of_tag t a b hp
 have h := (transformBranchGraph_eval idx hi _ _ _ _ _ _ _).mp
   (modelTransform_node_branch idx hi d t a b hb)
 rw [modelTransform_binary_left idx hi d t a b hn,modelTransform_binary_right idx hi d t a b hn] at h
 rcases ht with htag|htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h

lemma modelTransform_atomic (d t a b : M) (ht : t=1 ∨ t=2) :
 modelTransform idx hi d (modelSourceNode t a b)=modelSourceNode t
   (graphValue idx hi ![d,a])
   (graphValue idx hi ![d,b]) := by
 have hp : 0<t := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<1 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (0:Nat)<2 by decide))
 have hb : t<8 := by
   rcases ht with h|h
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (1:Nat)<8 by decide))
   · rw [h]; simpa using (model_natCast_lt (M := M) (show (2:Nat)<8 by decide))
 have hn := modelSourceNode_pos_of_tag t a b hp
 have h := (transformBranchGraph_eval idx hi _ _ _ _ _ _ _).mp
   (modelTransform_node_branch idx hi d t a b hb)
 rcases ht with htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h

lemma modelTransform_binder (d t a : M) (ht : t=6 ∨ t=7) :
 modelTransform idx hi d (modelSourceNode t a 0)=modelSourceNode t (modelTransform idx hi (d+1) a) 0 := by
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
 have hn := modelSourceNode_pos_of_tag t a 0 hp
 have h := (transformBranchGraph_eval idx hi _ _ _ _ _ _ _).mp
   (modelTransform_node_branch idx hi d t a 0 hb)
 rw [modelTransform_lookup idx hi (d+1) a _ (modelBinderIndex_descent d t a hgt)] at h
 rcases ht with htag|htag <;> subst t <;> simpa [ne_of_gt hn] using h


lemma modelTransform_malformed (d n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n])
 (hbad : ¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0))) :
 modelTransform idx hi d n=0 := by
 have h := (transformBranchGraph_eval idx hi _ _ _ _ _ _ _).mp
   (modelTransform_branch idx hi d n t a b ht ha hb)
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

end ZFR.ArithmeticRepresentation.GenericTransform
