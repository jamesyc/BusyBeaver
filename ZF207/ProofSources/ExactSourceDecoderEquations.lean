module
public import ExactSourceDecoderGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma sourceLeftGraph_eval (a n : M) : sourceLeftGraph.val.Evalb ![a,n] ↔
 ∃q,unpairLeftGraph.val.Evalb ![a,q] ∧ radix8QuotientGraph.val.Evalb ![q,n] := by
 rw [sourceLeftGraph,compositionGraph_eval]
 constructor
 · rintro ⟨w,ha,hw⟩
   have hv : w=![w 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
   exact ⟨w 0,by rw [hv] at ha; exact ha,hw 0⟩
 · rintro ⟨q,ha,hq⟩
   refine ⟨![q],ha,?_⟩
   intro i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact hq

lemma sourceRightGraph_eval (b n : M) : sourceRightGraph.val.Evalb ![b,n] ↔
 ∃q,unpairRightGraph.val.Evalb ![b,q] ∧ radix8QuotientGraph.val.Evalb ![q,n] := by
 rw [sourceRightGraph,compositionGraph_eval]
 constructor
 · rintro ⟨w,hb,hw⟩
   have hv : w=![w 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
   exact ⟨w 0,by rw [hv] at hb; exact hb,hw 0⟩
 · rintro ⟨q,hb,hq⟩
   refine ⟨![q],hb,?_⟩
   intro i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact hq

lemma source_decoder_reconstruction (n t a b : M)
 (ht : radix8ResidueGraph.val.Evalb ![t,n])
 (ha : sourceLeftGraph.val.Evalb ![a,n])
 (hb : sourceRightGraph.val.Evalb ![b,n]) : sourceNodeGraph.val.Evalb ![n,t,a,b] := by
 obtain ⟨hlt,q,hq⟩ := (radix8ResidueGraph_eval _ _).mp ht
 obtain ⟨q₁,ha,hq₁⟩ := (sourceLeftGraph_eval _ _).mp ha
 obtain ⟨q₂,hb,hq₂⟩ := (sourceRightGraph_eval _ _).mp hb
 obtain ⟨t₁,ht₁,hn₁⟩ := (radix8QuotientGraph_eval _ _).mp hq₁
 obtain ⟨t₂,ht₂,hn₂⟩ := (radix8QuotientGraph_eval _ _).mp hq₂
 have he₁ := (radix8_unique q₁ q t₁ t ht₁ hlt (hn₁.symm.trans hq)).1
 have he₂ := (radix8_unique q₂ q t₂ t ht₂ hlt (hn₂.symm.trans hq)).1
 subst q₁; subst q₂
 obtain ⟨b',hpa⟩ := (unpairLeftGraph_eval _ _).mp ha
 obtain ⟨a',hpb⟩ := (unpairRightGraph_eval _ _).mp hb
 have hpair := modelCantor_injective (hpa.symm.trans hpb)
 apply (sourceNodeGraph_eval _ _ _ _).mpr
 change n=8*modelCantor a b+t
 simpa only [hpa,hpair.2] using hq

lemma source_decoder_node (t a b : M) (ht : t<8) :
 radix8ResidueGraph.val.Evalb ![t,modelSourceNode t a b] ∧
 sourceLeftGraph.val.Evalb ![a,modelSourceNode t a b] ∧
 sourceRightGraph.val.Evalb ![b,modelSourceNode t a b] := by
 have hq : radix8QuotientGraph.val.Evalb ![modelCantor a b,modelSourceNode t a b] :=
   (radix8QuotientGraph_eval _ _).mpr ⟨t,ht,rfl⟩
 refine ⟨(radix8ResidueGraph_eval _ _).mpr ⟨ht,modelCantor a b,rfl⟩,?_,?_⟩
 · exact (sourceLeftGraph_eval _ _).mpr ⟨modelCantor a b,(unpairLeftGraph_eval _ _).mpr ⟨b,rfl⟩,hq⟩
 · exact (sourceRightGraph_eval _ _).mpr ⟨modelCantor a b,(unpairRightGraph_eval _ _).mpr ⟨a,rfl⟩,hq⟩

end ZFR.ArithmeticRepresentation
