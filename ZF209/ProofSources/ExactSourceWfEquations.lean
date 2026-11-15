module
public import ExactSourceWfModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelSourceWfCode_branch (n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n]) :
 wfBranchGraph.val.Evalb ![modelSourceWfCode n,(sourceWfHistory (M := M)).result ![] n,n,t,a,b] := by
 have he := modelSourceWfCode_step n
 unfold modelWfStep at he
 dsimp only at he
 have ht' := (graphValue_spec radix8ResidueGraph radix8ResidueGraph_total t ![n]).mp ht
 have ha' := (graphValue_spec sourceLeftGraph sourceLeftGraph_total a ![n]).mp ha
 have hb' := (graphValue_spec sourceRightGraph sourceRightGraph_total b ![n]).mp hb
 rw [←ht',←ha',←hb'] at he
 exact (graphValue_spec wfBranchGraph wfBranchGraph_total _ _).mpr he

lemma modelSourceWf_branch (n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n]) :
 modelSourceWf n ↔ modelWfAllowed ((sourceWfHistory (M := M)).result ![] n) n t a b := by
 have h := (wfBranchGraph_eval _ _ _ _ _ _).mp (modelSourceWfCode_branch n t a b ht ha hb)
 by_cases hp : modelWfAllowed ((sourceWfHistory (M := M)).result ![] n) n t a b
 · have hz : modelSourceWfCode n=1 := by simpa [hp] using h
   simp [modelSourceWf,hz,hp]
 · have hz : modelSourceWfCode n=0 := by simpa [hp] using h
   simp [modelSourceWf,hz,hp]

lemma modelSourceWf_zero : modelSourceWf (0:M) := by
 obtain ⟨t,ht,_⟩ := radix8ResidueGraph_total (M := M) ![0]
 obtain ⟨a,ha,_⟩ := sourceLeftGraph_total (M := M) ![0]
 obtain ⟨b,hb,_⟩ := sourceRightGraph_total (M := M) ![0]
 apply (modelSourceWf_branch 0 t a b ht ha hb).mpr
 exact Or.inl rfl

lemma modelSourceWf_node (t a b : M) (ht : t<8) (hn : 0<modelSourceNode t a b) :
 modelSourceWf (modelSourceNode t a b) ↔
 (t=1 ∨ t=2) ∨ ((t=3 ∨ t=4 ∨ t=5) ∧ modelSourceWf a ∧ modelSourceWf b) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ modelSourceWf a) := by
 obtain ⟨ht,ha,hb⟩ := source_decoder_node t a b ht
 rw [modelSourceWf_branch _ _ _ _ ht ha hb]
 unfold modelWfAllowed
 rw [modelSourceWfCode_lookup a _ (modelSourceNode_left_lt t a b hn),
   modelSourceWfCode_lookup b _ (modelSourceNode_right_lt t a b hn)]
 simp only [ne_of_gt hn,false_or,modelSourceWf]

end ZFR.ArithmeticRepresentation
