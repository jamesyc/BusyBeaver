module
public import ZF192.Machine.Control.Checks
public import ZF192.Simulation.Standard.FrameEncoding
public import ZF192.Simulation.Forward.HistoryLift
@[expose] public section
/-! # The arithmetic frame relation

`FrameRelation a b`: `a` codes a native source state at some site `pc < 4341` and `b` codes
the physical frame of that state for some padding `n` and right tail `ρ`. The relation is
defined by an arithmetic formula, as the history induction requires. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF192.BinaryTape M192.Window M192.Paths M192.Control
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
  cases b <;> simp [prefixGraph,bitPrefix,bitValue,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,Matrix.constant_eq_singleton,ih,Matrix.empty_eq,numeral_eq_natCast]
/-- `z = blk v t`. -/
def blockGraph : ArithmeticSemisentence 3 := “z v t. !bitRunGraph z (v+1) 1 (2*t)”
lemma blockGraph_eval (z v t:M) : blockGraph.Evalb ![z,v,t] ↔ z=blk v t := by
 simp [blockGraph,blk,ones,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,Matrix.constant_eq_singleton,
 Matrix.empty_eq,bitRun_defined.iff,numeral_eq_natCast]
noncomputable def frameAtGraph (pc:Nat) : ArithmeticSemisentence 2 :=
 “native physical. ∃n, ∃rho, ∃a0, ∃a1, ∃a2, ∃a3, ∃a4, ∃a5, ∃a6, ∃a7, ∃a8,
 !ZF192Support.NativeSource.stateGraph native ↑pc a0 a1 a2 a3 a4 a5 a6 a7 a8 ∧
 ∃u8, !blockGraph u8 a1 0 ∧ ∃u7, !blockGraph u7 a5 u8 ∧ ∃u6, !blockGraph u6 a8 u7 ∧
 ∃u5, !blockGraph u5 a7 u6 ∧ ∃u4, !blockGraph u4 a3 u5 ∧ ∃u3, !blockGraph u3 a4 u4 ∧
 ∃u2, !blockGraph u2 a0 u3 ∧ ∃u1, !blockGraph u1 a2 u2 ∧ ∃u0, !blockGraph u0 a6 u1 ∧
 ∃pad, !bitRunGraph pad n 1 (2*(2*u0)) ∧
 ∃left, !(prefixGraph (winL (fpath (align pc)))) left pad ∧ ∃right, !(prefixGraph (winR (fpath (align pc)))) right rho ∧
 !BinaryTape.stateGraph physical ↑M192.root left right”
def FrameAt (pc:Nat) (a b:M) : Prop := ∃n ρ:M,∃r:Fin 9→M,
 a=ZF192Support.NativeSource.stateCode ⟨(pc:M),r⟩ ∧ b=BinaryTape.stateCode (nativeFrame (align pc) (permute r) n ρ)
private theorem regList_permute (r : Fin 9 → M) :
    regList (permute r) = [r 6, r 2, r 0, r 4, r 3, r 7, r 8, r 5, r 1] := rfl

lemma frameAtGraph_eval (pc:Nat) (a b:M) : (frameAtGraph pc).Evalb ![a,b]↔FrameAt pc a b := by
 simp only [frameAtGraph,Semiformula.eval_rew]
 simp [Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,Matrix.constant_eq_singleton,
 ZF192Support.NativeSource.stateGraph_eval,blockGraph_eval,bitRun_defined.iff,prefixGraph_eval,
 BinaryTape.stateGraph_eval,numeral_eq_natCast,FrameAt,nativeFrame,cell,regList_permute,file,ones]
 constructor
 · rintro ⟨n,ρ,a0,a1,a2,a3,a4,a5,a6,a7,a8,ha,hb⟩
   exact ⟨n,ρ,![a0,a1,a2,a3,a4,a5,a6,a7,a8],ha,hb⟩
 · rintro ⟨n,ρ,r,ha,hb⟩
   refine ⟨n,ρ,r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,?_,hb⟩
   have eta:r=![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8] := by
    funext j;rcases j with ⟨j,hj⟩
    have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
    rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> rfl
   simpa only [←eta] using ha
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
end ZF192.NativePhysicalLift
