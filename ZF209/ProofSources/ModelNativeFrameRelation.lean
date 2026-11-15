module
public import ModelNativeFrameEncoding
public import ModelRegisterFileGraphs
public import ModelNativePhysicalHistoryLift
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF209.BinaryTape
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def prefixGraph : List Bool→ArithmeticSemisentence 2
 | []=>“z tail. z=tail”
 | false::bs=> “z tail. ∃r, !(prefixGraph bs) r tail ∧ z=2*r”
 | true::bs=> “z tail. ∃r, !(prefixGraph bs) r tail ∧ z=1+2*r”
lemma prefixGraph_eval (path:List Bool) (z tail:M) :
 (prefixGraph path).Evalb ![z,tail] ↔ z=bitPrefix path tail := by
 induction path generalizing z with
 | nil=>simp [prefixGraph,bitPrefix]
 | cons b bs ih=>
  have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _;subst i;rfl
  cases b <;> simp [prefixGraph,bitPrefix,bitValue,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,hv,ih,Matrix.empty_eq,numeral_eq_natCast]
noncomputable def frameAtGraph (pc:Nat) : ArithmeticSemisentence 2 :=
 “native physical. ∃gap, ∃spares, ∃a0, ∃a1, ∃a2, ∃a3, ∃a4, ∃a5, ∃a6, ∃a7, ∃a8,
 !NativeSource.stateGraph native ↑pc a0 a1 a2 a3 a4 a5 a6 a7 a8 ∧
 ∃file, !registerFileGraph file a0 a1 a2 a3 a4 a5 a6 a7 a8 (spares+1) ∧
 ∃bits, !bitRunGraph bits (gap+↑(48-(M209.Source.paths pc).length)) 0 (1+2*file) ∧
 ∃right, !(prefixGraph (M209.Source.paths pc)) right bits ∧
 !BinaryTape.stateGraph physical ↑(M209.forward (M209.inverse 74)) 1 right”
def FrameAt (pc:Nat) (a b:M) : Prop := ∃gap spares:M,∃r:Fin 9→M,
 a=NativeSource.stateCode ⟨(pc:M),r⟩ ∧ b=BinaryTape.stateCode (nativeFrame pc gap r (spares+1))
lemma frameAtGraph_eval (pc:Nat) (a b:M) : (frameAtGraph pc).Evalb ![a,b]↔FrameAt pc a b := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i;have hi:i=0:=Subsingleton.elim _ _;subst i;rfl
 simp only [frameAtGraph,Semiformula.eval_rew]
 simp [Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hv,
 NativeSource.stateGraph_eval,registerFile_defined.iff,bitRun_defined.iff,prefixGraph_eval,
 BinaryTape.stateGraph_eval,numeral_eq_natCast,FrameAt,nativeFrame,namedState]
 constructor
 · rintro ⟨g,s,a0,a1,a2,a3,a4,a5,a6,a7,a8,ha,hb⟩
   exact ⟨g,s,![a0,a1,a2,a3,a4,a5,a6,a7,a8],ha,hb⟩
 · rintro ⟨g,s,r,ha,hb⟩
   have eta:r=![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8] := by
    funext j;rcases j with ⟨j,hj⟩
    have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
    rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
   refine ⟨g,s,r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,?_,?_⟩
   · simpa only [←eta] using ha
   · have ef:(fun i:Fin 9=>![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,s+1] i.castSucc)=r := by
      funext j;rcases j with ⟨j,hj⟩
      have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
      rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
     simpa only [ef] using hb
noncomputable def frameTableGraph (sites:List Nat) : ArithmeticSemisentence 2 :=
 sites.foldr (fun pc rest=>frameAtGraph pc ⋎ rest) ⊥
lemma frameTableGraph_eval (sites:List Nat) (a b:M) :
 (frameTableGraph sites).Evalb ![a,b]↔∃pc∈sites,FrameAt pc a b := by
 induction sites with
 | nil=>simp [frameTableGraph]
 | cons pc rest ih=>
  change ((frameAtGraph pc).Evalb ![a,b]∨(frameTableGraph rest).Evalb ![a,b])↔_
  rw [frameAtGraph_eval,ih];simp
noncomputable def frameRelationGraph : ArithmeticSemisentence 2 := frameTableGraph (List.range 4341)
def FrameRelation (a b:M) : Prop := ∃pc:Nat,pc<4341 ∧ FrameAt pc a b
lemma frameRelationGraph_eval (a b:M) : frameRelationGraph.Evalb ![a,b]↔FrameRelation a b := by
 change (frameTableGraph (List.range 4341)).Evalb ![a,b]↔_
 rw [frameTableGraph_eval];simp only [List.mem_range,FrameRelation]
end ZF209.NativePhysicalLift
