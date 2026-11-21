module
public import I3_380.EquationModel
@[expose] public section

namespace PalomarI3380.Logic.Expanded.EquationModel

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop}
variable (L : ClassAxioms E G) (inhabited : Nonempty V)

local notation "K" => (L.context inhabited)
local notation "R" => ClassRelation E G
local infixl:70 " ⋆ " => ClassRelation.product

private theorem image_law (minimum : ClassMinimum E G) (r : R) :
    let img := ClassRelation.member.converse ⋆ select L inhabited r
    (img ⋆ ClassRelation.member.complement).complement.meet
      (img.complement ⋆ ClassRelation.member).complement ⋆ ClassRelation.top = ClassRelation.top := by
  dsimp only
  apply ClassRelation.ext
  intro x y
  let chosen := select L inhabited r
  let img := ClassRelation.member.converse ⋆ chosen
  change (∃ a, ((¬∃ z, img.holds x z ∧ ¬E z a) ∧
    (¬∃ z, ¬img.holds x z ∧ E z a)) ∧ True) ↔ True
  obtain ⟨range,members⟩ := L.replacement chosen.holds chosen.definable
    (fun _ _ _ => select_function L inhabited minimum r) x
  exact ⟨fun _ => trivial,fun _ => ⟨range,
    ⟨fun ⟨z,positive,negative⟩ => negative ((members z).mpr positive),
     fun ⟨z,negative,positive⟩ => negative ((members z).mp positive)⟩,trivial⟩⟩

private theorem subset_law :
    (ClassRelation.subset : R) =
      (ClassRelation.member.converse ⋆ ClassRelation.member.complement).complement := by
  classical
  apply ClassRelation.ext
  intro x y
  change (∀ z, E z x → E z y) ↔ ¬∃ z, E z x ∧ ¬E z y
  exact ⟨fun h ⟨z,mem,notMem⟩ => notMem (h z mem),fun h z mem =>
    Classical.byContradiction fun notMem => h ⟨z,mem,notMem⟩⟩

private theorem domain_law {stage j : V} (mapping : Internal.FunctionInto E j stage stage) :
    (ClassRelation.rankDiagonal stage : R) =
      ClassRelation.one.meet (embedding L inhabited j ⋆ ClassRelation.top) := by
  apply ClassRelation.ext
  intro x y
  change (x = y ∧ E x stage) ↔ x = y ∧ ∃ z, Internal.At E j x z ∧ True
  constructor
  · rintro ⟨same,inside⟩
    obtain ⟨z,edge,_⟩ := mapping.1.1 x inside
    exact ⟨same,z,edge,trivial⟩
  · rintro ⟨same,z,edge,_⟩
    exact ⟨same,SetRecursion.at_domain (N := (K)) mapping.1 edge⟩

private theorem closed_law {height stage : V} (rank : (K).Rank height stage)
    (limit : Internal.Inductive E height) :
    (ClassRelation.rankDiagonal stage : R) = ClassRelation.one.meet
      (ClassRelation.member ⋆ (stages L inhabited).meet (ClassRelation.rankDiagonal stage) ⋆ ClassRelation.top) := by
  apply ClassRelation.ext
  intro x y
  change (x = y ∧ E x stage) ↔ x = y ∧
    ∃ v, (∃ t, E x t ∧ (t = v ∧ ∃ b, (K).Rank b t) ∧ t = v ∧ E t stage) ∧ True
  refine and_congr Iff.rfl ((K).rank_limit_cover rank limit x |>.trans ?_)
  exact ⟨fun ⟨t,xt,ts,atRank⟩ => ⟨t,⟨t,xt,⟨rfl,atRank⟩,rfl,ts⟩,trivial⟩,
    fun ⟨_,⟨t,xt,⟨_,atRank⟩,_,ts⟩,_⟩ => ⟨t,xt,ts,atRank⟩⟩

private theorem preserves_law {w height stage j : V} (omega : Internal.Omega E w)
    (rank : (K).Rank height stage) (mapping : Internal.FunctionInto E j stage stage)
    (elementary : Internal.ElementaryOnRank E w stage j) (t : LocalTree) :
    ((embedding L inhabited j).converse ⋆ LocalTree.relation stage t ⋆
      embedding L inhabited j).meet (LocalTree.relation stage t).complement =
        ClassRelation.top.complement := by
  apply ClassRelation.ext
  intro x y
  change ((∃ b, (∃ a, Internal.At E j a x ∧ (LocalTree.relation (G := G) stage t).holds a b) ∧
    Internal.At E j b y) ∧ ¬(LocalTree.relation (G := G) stage t).holds x y) ↔ ¬True
  refine ⟨fun ⟨⟨_,⟨_,left,edge⟩,right⟩,bad⟩ _ => ?_,fun h => (h trivial).elim⟩
  exact bad (LocalTree.preserves L inhabited omega mapping elementary ((K).rank_transitive rank)
    t edge left right)

private theorem complement_nand (r s : R) : (r.nand s).complement = r.meet s := by
  classical
  exact ClassRelation.ext fun _ _ => Classical.not_not

open Manifest in
set_option maxHeartbeats 1500000 in
theorem models_preceding {w height stage j : V} (omega : Internal.Omega E w)
    (rank : (K).Rank height stage) (limit : Internal.Inductive E height)
    (mapping : Internal.FunctionInto E j stage stage)
    (elementary : Internal.ElementaryOnRank E w stage j)
    (minimum : ClassMinimum E G) : (algebra L inhabited stage j).Models preceding := by
  intro e h v
  simp only [preceding,List.cons_append,List.nil_append,retained,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst e
    simp only [meredith1,meredith2,defineSubset,defineStages,productAssociative,rightIdentity,
      converseInvolution,productMonotonicity,converseMeet,peirce,extensionality,choiceSub,
      choiceFunctional,choiceDomain,imageEquation,defineDomain,stageLaw,domainClosed,Manifest.a,
      Manifest.b,Manifest.c,Manifest.meet,Manifest.subset,Manifest.stage,Algebra.eval,algebra,ClassRelation.algebra,complement_nand]
  · apply ClassRelation.ext
    intro x y
    change (¬(¬(v 0).holds x y ∧ (v 1).holds x y) ∧ (v 0).holds x y) ↔ _
    exact ⟨And.right,fun h => ⟨fun nh => nh.1 h,h⟩⟩
  · apply ClassRelation.ext
    intro x y
    change (¬(¬(v 0).holds x y ∧ (v 1).holds x y) ∧ (v 2).holds x y ∧ (v 1).holds x y) ↔
      (v 1).holds x y ∧ (v 2).holds x y ∧ (v 0).holds x y
    classical
    exact ⟨fun ⟨h,c,b⟩ => ⟨b,c,Classical.byContradiction fun a => h ⟨a,b⟩⟩,
      fun ⟨b,c,a⟩ => ⟨fun bad => bad.1 a,c,b⟩⟩
  · exact subset_law
  · change stages L inhabited = (select L inhabited (.subset : R)).converse ⋆ select L inhabited .subset
    rw [select_subset]
    exact (stages_are_range L inhabited).symm
  · apply ClassRelation.ext
    intro x y
    change (∃ i, (v 0).holds x i ∧ ∃ k, (v 1).holds i k ∧ (v 2).holds k y) ↔
      ∃ k, (∃ i, (v 0).holds x i ∧ (v 1).holds i k) ∧ (v 2).holds k y
    exact ⟨fun ⟨i,hi,k,hk,hy⟩ => ⟨k,⟨i,hi,hk⟩,hy⟩,
      fun ⟨k,⟨i,hi,hk⟩,hy⟩ => ⟨i,hi,k,hk,hy⟩⟩
  · apply ClassRelation.ext
    intro x y
    change (∃ z, (v 0).holds x z ∧ z = y) ↔ _
    exact ⟨fun ⟨_,h,rfl⟩ => h,fun h => ⟨y,h,rfl⟩⟩
  · exact ClassRelation.ext fun _ _ => Iff.rfl
  · apply ClassRelation.ext
    intro x y
    change ((∃ z, (v 0).holds x z ∧ (v 1).holds z y) ∧
      (∃ z, (v 0).holds x z ∧ (v 2).holds z y ∧ (v 1).holds z y)) ↔
        ∃ z, (v 0).holds x z ∧ (v 2).holds z y ∧ (v 1).holds z y
    exact ⟨And.right,fun h@⟨z,r,_,s⟩ => ⟨⟨z,r,s⟩,h⟩⟩
  · apply ClassRelation.ext
    intro x y
    rfl
  · apply ClassRelation.ext
    intro x y
    change ((∃ z, (v 0).holds z x ∧ ¬∃ i, (v 0).holds z i ∧ (v 1).holds i y) ∧
      (v 1).holds x y) ↔ ¬True
    exact ⟨fun ⟨⟨z,edge,missing⟩,mem⟩ _ => missing ⟨x,edge,mem⟩,fun h => (h trivial).elim⟩
  · apply ClassRelation.ext
    intro x y
    change ((K).Subset x y ∧ (K).Subset y x) ↔ x = y
    exact ⟨fun h => (K).ext x y fun z => ⟨h.1 z,h.2 z⟩,
      fun h => by cases h; exact ⟨(K).subset_refl _, (K).subset_refl _⟩⟩
  · apply ClassRelation.ext
    intro x y
    change ((select L inhabited (v 0)).holds x y ∧ (v 0).holds x y) ↔ _
    exact ⟨And.left, fun h => ⟨h,select_sub L inhabited (v 0) h⟩⟩
  · apply ClassRelation.ext
    intro x y
    change ((∃ z, (select L inhabited (v 0)).holds z x ∧ (select L inhabited (v 0)).holds z y) ∧ x ≠ y) ↔ ¬True
    exact ⟨fun ⟨⟨_,left,right⟩,different⟩ _ =>
      different (select_function L inhabited minimum _ left right),fun h => (h trivial).elim⟩
  · apply ClassRelation.ext
    intro x y
    change (∃ z, (select L inhabited (v 0)).holds x z ∧ True) ↔ ∃ z, (v 0).holds x z ∧ True
    constructor
    · rintro ⟨z,h,_⟩
      exact ⟨z,select_sub L inhabited (v 0) h,trivial⟩
    · rintro ⟨z,h,_⟩
      obtain ⟨s,chosen⟩ := select_exists L inhabited minimum omega (v 0) x ⟨z,h⟩
      exact ⟨s,chosen,trivial⟩
  · exact image_law L inhabited minimum (v 0)
  · exact domain_law L inhabited mapping
  · exact stages_law L inhabited
  · exact closed_law L inhabited rank limit
  · change LocalTree.relation stage (LocalTree.decode (K) (LocalTree.encode (K) .leaf)) = _
    rw [LocalTree.decode_encode]
    rfl
  · change LocalTree.relation stage (LocalTree.decode (K) (LocalTree.encode (K) _)) = _
    rw [LocalTree.decode_encode]
    rfl
  · exact preserves_law L inhabited omega rank mapping elementary (LocalTree.decode (K) (v 0))

include L inhabited in
theorem underivability (minimum : ClassMinimum E G) (large : Internal.HasI3 E) :
    ¬ Derives Manifest.final (.const .D) (.const .J) := by
  obtain ⟨w,a,stage,j,omega,rank,limit,embeddingInto,⟨x,y,_,_,edge,different⟩,elementary⟩ := large
  have realRank := (K).rank_from_internal (L.ordinary.foundation (fun _ => (K).empty)) rank
  let M := algebra L inhabited stage j
  have model := (M.models_final_of_preceding
    (models_preceding L inhabited omega realRank limit embeddingInto elementary minimum))
  intro proof
  have equality := Derives.sound M model proof
  change (ClassRelation.rankDiagonal stage : R) = embedding L inhabited j at equality
  have fromGraph : (embedding L inhabited j).holds x y := edge
  rw [← equality] at fromGraph
  exact different fromGraph.1

end PalomarI3380.Logic.Expanded.EquationModel
