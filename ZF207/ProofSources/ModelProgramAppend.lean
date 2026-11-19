module
public import ModelProgramReverse
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
instance programReverseOnto_definable : 𝚺ᴬ₁-Function₂ (programReverseOnto (M:=M)) := by
 unfold programReverseOnto; definability
noncomputable def programAppend (n b:M) : M := programReverseOnto (programReverseOnto n 0) b
instance programAppend_definable : 𝚺ᴬ₁-Function₂ (programAppend (M:=M)) := by
 unfold programAppend; definability
lemma programAppend_zero (b:M) : programAppend 0 b=b := by simp only [programAppend,programReverseOnto_zero]
lemma residual_reconstruct (n:M) (hn:n≠0) :
 commandCode (parseCommand (modelPredecessor n)).1 (parseCommand (modelPredecessor n)).2+1=n := by
 rw [commandCode_parse,modelPredecessor_of_pos n (pos_iff_ne_zero.mpr hn)]
lemma programReverseOnto_reverseOnto (n:M) : ∀ b c:M,
 programReverseOnto (programReverseOnto n b) c=programReverseOnto b (programAppend n c) := by
 induction n using ISigma1.pi1_order_induction
 · definability
 case ind n ih =>
  by_cases hn:n=0
  · subst n; intro b c; simp only [programReverseOnto_zero,programAppend_zero]
  · have hrec:=residual_reconstruct n hn
    have hlt:(parseCommand (modelPredecessor n)).2<n := by
     simpa only [hrec] using command_residual_descends (parseCommand (modelPredecessor n)).1 (parseCommand (modelPredecessor n)).2
    have hh:=ih (parseCommand (modelPredecessor n)).2 hlt
    intro b c
    nth_rw 1 [←hrec]
    rw [programReverseOnto_cons,hh,programReverseOnto_cons]
    congr 1
    conv_rhs => rw [←hrec]
    simp only [programAppend,programReverseOnto_cons]
    conv_rhs => rw [hh,programReverseOnto_cons,programReverseOnto_zero]
    rfl
lemma programAppend_cons (c:Command M) (n b:M) :
 programAppend (commandCode c n+1) b=commandCode c (programAppend n b)+1 := by
 simp only [programAppend,programReverseOnto_cons]
 rw [programReverseOnto_reverseOnto,programReverseOnto_cons,programReverseOnto_zero]
 rfl
end ZF207.ModelCommands
