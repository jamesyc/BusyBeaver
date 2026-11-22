module
public import ZF192.Tape.Determinism
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma even_or_odd (n:M) : ∃q,n=2*q ∨ n=2*q+1 := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact ⟨0,Or.inl (by simp)⟩
 case succ n ih =>
  obtain ⟨q,hq|hq⟩:=ih
  · exact ⟨q,Or.inr (by rw [hq])⟩
  · refine ⟨q+1,Or.inl ?_⟩
    rw [hq,mul_add,mul_one,add_assoc]
    congr 1
    norm_num
lemma bits_surjective (n:M) : ∃b:Bool,∃tail:M,n=bitValue b+2*tail := by
 obtain ⟨q,hq|hq⟩:=even_or_odd n
 · exact ⟨false,q,by simpa [bitValue] using hq⟩
 · exact ⟨true,q,by simpa [bitValue,add_comm] using hq⟩
def lowBitGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “b n. (b=0 ∨ b=1) ∧ ∃tail,n=b+2*tail”
def tailBitsGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “tail n. n=2*tail ∨ n=1+2*tail”
lemma lowBitGraph_eval (b n:M) : lowBitGraph.val.Evalb ![b,n] ↔
 ∃read:Bool,∃tail:M,b=bitValue read ∧ n=bitValue read+2*tail := by
 simp [lowBitGraph,bitValue]
 constructor
 · rintro ⟨hb,tail,he⟩
   rcases hb with rfl|rfl
   · exact Or.inl ⟨rfl,tail,by simpa using he⟩
   · exact Or.inr ⟨rfl,tail,he⟩
 · rintro (⟨rfl,tail,he⟩|⟨rfl,tail,he⟩)
   · exact ⟨Or.inl rfl,tail,by simpa using he⟩
   · exact ⟨Or.inr rfl,tail,he⟩
lemma tailBitsGraph_eval (tail n:M) : tailBitsGraph.val.Evalb ![tail,n] ↔
 ∃read:Bool,n=bitValue read+2*tail := by simp [tailBitsGraph,bitValue]
lemma lowBitGraph_total : GraphTotalIn (M:=M) lowBitGraph := by
 intro v
 rw [Matrix.fun_eq_vec_one v]
 obtain ⟨b,tail,he⟩:=bits_surjective (v 0)
 refine ⟨bitValue b,(lowBitGraph_eval _ _).mpr ⟨b,tail,rfl,he⟩,?_⟩
 intro z hz
 obtain ⟨b',tail',rfl,he'⟩:=(lowBitGraph_eval z _).mp hz
 have hb:=(binary_decomp_unique _ _ _ _ (he'.symm.trans he)).1
 rw [hb]
lemma tailBitsGraph_total : GraphTotalIn (M:=M) tailBitsGraph := by
 intro v
 rw [Matrix.fun_eq_vec_one v]
 obtain ⟨b,tail,he⟩:=bits_surjective (v 0)
 refine ⟨tail,(tailBitsGraph_eval _ _).mpr ⟨b,he⟩,?_⟩
 intro z hz
 obtain ⟨b',he'⟩:=(tailBitsGraph_eval z _).mp hz
 exact (binary_decomp_unique _ _ _ _ (he'.symm.trans he)).2
noncomputable def lowBit (n:M) : M := graphValue lowBitGraph lowBitGraph_total ![n]
noncomputable def tailBits (n:M) : M := graphValue tailBitsGraph tailBitsGraph_total ![n]
lemma lowBit_cons (b:Bool) (tail:M) : lowBit (bitValue b+2*tail)=bitValue b := by
 symm
 exact (graphValue_spec lowBitGraph lowBitGraph_total _ ![_]).mp ((lowBitGraph_eval _ _).mpr ⟨b,tail,rfl,rfl⟩)
lemma tailBits_cons (b:Bool) (tail:M) : tailBits (bitValue b+2*tail)=tail := by
 symm
 exact (graphValue_spec tailBitsGraph tailBitsGraph_total _ ![_]).mp ((tailBitsGraph_eval _ _).mpr ⟨b,rfl⟩)
end ZF192.BinaryTape
