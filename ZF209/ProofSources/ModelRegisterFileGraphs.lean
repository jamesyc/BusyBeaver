module
public import ModelRegisterFileEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def registerBlockGraphOf (runs:𝚺ᴬ₁.Semisentence 4) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z value tail. ∃r, !runs r (value+1) 1 tail ∧ z=2*r”
def registerBlockGraph : 𝚺ᴬ₁.Semisentence 3 := registerBlockGraphOf bitRunGraph
lemma registerBlockGraphOf_eval (runs:𝚺ᴬ₁.Semisentence 4) (f:M→M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₃ f runs) (v:Fin 3→M) :
 (registerBlockGraphOf runs).val.Evalb v ↔ v 0=2*f (v 1+1) 1 (v 2) := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [registerBlockGraphOf,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,hf.iff]
lemma registerBlock_defined : 𝚺ᴬ₁.DefinedFunction₂ (registerBlock (M:=M)) registerBlockGraph := .mk (by
 intro v; exact registerBlockGraphOf_eval _ _ bitRun_defined v)
instance registerBlock_definable : 𝚺ᴬ₁-Function₂ (registerBlock (M:=M)) := registerBlock_defined.to_definable
/-- Exactly nine primary blocks, not a standard-length stand-in for spare count. -/
def primaryBlocksGraphOf (block:𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 11 := .mkSigma
 “z a0 a1 a2 a3 a4 a5 a6 a7 a8 tail.
 ∃u1, !block z a0 u1 ∧ ∃u2, !block u1 a1 u2 ∧
 ∃u3, !block u2 a2 u3 ∧ ∃u4, !block u3 a3 u4 ∧
 ∃u5, !block u4 a4 u5 ∧ ∃u6, !block u5 a5 u6 ∧
 ∃u7, !block u6 a6 u7 ∧ ∃u8, !block u7 a7 u8 ∧ !block u8 a8 tail”
def primaryBlocksGraph : 𝚺ᴬ₁.Semisentence 11 := primaryBlocksGraphOf registerBlockGraph
lemma primaryBlocksGraphOf_eval (block:𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f block) (v:Fin 11→M) :
 (primaryBlocksGraphOf block).val.Evalb v ↔
 v 0=f (v 1) (f (v 2) (f (v 3) (f (v 4) (f (v 5) (f (v 6) (f (v 7) (f (v 8) (f (v 9) (v 10))))))))) := by
 simp [primaryBlocksGraphOf,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hf.iff]
lemma primaryBlocks_defined : 𝚺ᴬ₁.DefinedFunction
 (fun v:Fin 10→M=>primaryBlocks (fun i=>v i.castSucc) (v 9)) primaryBlocksGraph := .mk (by
 intro v; exact primaryBlocksGraphOf_eval _ _ registerBlock_defined v)
/-- Eleven inputs: nine primary values, model-sized spare count, arbitrary suffix. -/
def registerFileWithTailGraphOf (primary:𝚺ᴬ₁.Semisentence 11) (spares:𝚺ᴬ₁.Semisentence 3) :
 𝚺ᴬ₁.Semisentence 12 := .mkSigma
 “z a0 a1 a2 a3 a4 a5 a6 a7 a8 n tail.
 ∃s, !spares s n tail ∧ !primary z a0 a1 a2 a3 a4 a5 a6 a7 a8 s”
def registerFileWithTailGraph : 𝚺ᴬ₁.Semisentence 12 :=
 registerFileWithTailGraphOf primaryBlocksGraph spareRunGraph
lemma registerFileWithTailGraphOf_eval (primary:𝚺ᴬ₁.Semisentence 11) (spares:𝚺ᴬ₁.Semisentence 3)
 (p:(Fin 10→M)→M) (s:M→M→M) (hp:𝚺ᴬ₁.DefinedFunction p primary)
 (hs:𝚺ᴬ₁.DefinedFunction₂ s spares) (v:Fin 12→M) :
 (registerFileWithTailGraphOf primary spares).val.Evalb v ↔
 v 0=p ![v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,s (v 10) (v 11)] := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [registerFileWithTailGraphOf,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,hv,hp.iff,hs.iff]
lemma registerFileWithTail_defined : 𝚺ᴬ₁.DefinedFunction
 (fun v:Fin 11→M=>registerFileWithTail (fun i=>v i.castSucc.castSucc) (v 9) (v 10))
 registerFileWithTailGraph := .mk (by
 intro v
 exact registerFileWithTailGraphOf_eval _ _ _ _ primaryBlocks_defined spareRun_defined v)
attribute [irreducible] registerFileWithTailGraph
def registerFileGraph : 𝚺ᴬ₁.Semisentence 11 :=
 registerFileWithTailGraph.rew (Rew.bind (L:=ℒₒᵣ)
  ![#0,#1,#2,#3,#4,#5,#6,#7,#8,#9,#10,‘0’] Empty.elim)
lemma registerFile_defined : 𝚺ᴬ₁.DefinedFunction
 (fun v:Fin 10→M=>registerFile (fun i=>v i.castSucc) (v 9)) registerFileGraph := .mk (by
 intro v
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [registerFileGraph,registerFile,registerFileWithTail,primaryBlocks,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hv,registerFileWithTail_defined.iff])
end ZF209.BinaryTape
