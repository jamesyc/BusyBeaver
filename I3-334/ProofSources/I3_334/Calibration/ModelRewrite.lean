module
public import I3_334.Calibration.ModelTermSyntax
public import I3_334.Search.Templates
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceWords (appendVector appendVector_assoc)
open Templates (Pattern equations)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Interpret the fixed templates on arithmetically coded ground words. -/
noncomputable def modelTemplate (values : M) : Pattern → M
  | .capture i => values.[(i.val : M)]
  | .constant tag => modelApplication (tag : M) []
  | .unary tag t => modelApplication (tag : M) [modelTemplate values t]
  | .binary tag t u => modelApplication (tag : M) [modelTemplate values t,modelTemplate values u]

theorem modelTemplate_definable (p : Pattern) : 𝚺ᴬ₁-Function₁ (fun v : M => modelTemplate v p) := by
  induction p with
  | capture slot =>
    simp only [modelTemplate]
    definability
  | constant tag =>
    simp only [modelTemplate]
    definability
  | unary tag p ih =>
    simp only [modelTemplate,modelApplication,joinVectors,ArithmeticMachine.SourceWords.appendVector_empty_suffix]
    definability
  | binary tag p q ip iq =>
    simp only [modelTemplate,modelApplication,joinVectors,ArithmeticMachine.SourceWords.appendVector_empty_suffix]
    definability

def ModelSubstitution (v : M) : Prop :=
  len v = 4 ∧ ClosedVector 0 v.[0] ∧ ClosedVector 0 v.[1] ∧
    ClosedVector 0 v.[2] ∧ ClosedVector 3 v.[3]

theorem modelSubstitution_definable : 𝚺ᴬ₁-Predicate (ModelSubstitution (M := M)) := by
  have closed := closedVector_definable (M := M)
  unfold ModelSubstitution
  definability

noncomputable def contextWord (front word rest : M) : M :=
  appendVector front (appendVector word rest)

def modelMatch (p : Pattern) (values front rest word : M) : Prop :=
  word = contextWord front (modelTemplate values p) rest

def modelInstance (e : Templates.Equation) (old new : M) : Prop :=
  ∃ values front rest : M, ModelSubstitution values ∧
    ((modelMatch e.1 values front rest old ∧ modelMatch e.2 values front rest new) ∨
      (modelMatch e.2 values front rest old ∧ modelMatch e.1 values front rest new))

theorem contextWord_definable : 𝚺ᴬ₁-Function₃ (contextWord (M := M)) := by
  unfold contextWord
  definability

theorem modelMatch_definable (p : Pattern) : 𝚺ᴬ₁-Relation₄ (modelMatch (M := M) p) := by
  letI : 𝚺ᴬ₁-Function₁ (fun v : M => modelTemplate v p) := modelTemplate_definable p
  letI : 𝚺ᴬ₁-Function₃ (contextWord (M := M)) := contextWord_definable
  have value : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 3 → M => modelTemplate (v 0) p) :=
    Bounding.HierarchySymbol.DefinableFunction₁.comp (F := fun u => modelTemplate u p) (.var 0)
  have word : 𝚺ᴬ₁-Function₃ (fun (v l r : M) => contextWord l (modelTemplate v p) r) :=
    Bounding.HierarchySymbol.DefinableFunction₃.comp (F := contextWord) (.var 1) value (.var 2)
  have graph : 𝚺ᴬ₁.Definable (fun v : Fin 4 → M =>
      v 0 = contextWord (v 2) (modelTemplate (v 1) p) (v 3)) := word
  exact graph.retraction (![3,0,1,2] : Fin 4 → Fin 4)

theorem modelInstance_definable (e : Templates.Equation) : 𝚺ᴬ₁-Relation (modelInstance (M := M) e) := by
  have values := modelSubstitution_definable (M := M)
  have lhs := modelMatch_definable (M := M) e.1
  have rhs := modelMatch_definable (M := M) e.2
  have body : 𝚺ᴬ₁.Definable (fun v : Fin 5 → M =>
      ModelSubstitution (v 2) ∧
        ((modelMatch e.1 (v 2) (v 1) (v 0) (v 3) ∧ modelMatch e.2 (v 2) (v 1) (v 0) (v 4)) ∨
         (modelMatch e.2 (v 2) (v 1) (v 0) (v 3) ∧ modelMatch e.1 (v 2) (v 1) (v 0) (v 4)))) :=
    (values.retraction (fun _ => 2)).and
      (((lhs.retraction ![2,1,0,3]).and (rhs.retraction ![2,1,0,4])).or
        ((rhs.retraction ![2,1,0,3]).and (lhs.retraction ![2,1,0,4])))
  exact body.exs.exs.exs

/-- A rewrite record includes both the context and the syntactic guard on
the fourth substitution. All witnesses may be internal arithmetic words. -/
def ModelRewrite (old new : M) : Prop :=
  ∃ e ∈ equations, modelInstance e old new

theorem modelRewrite_definable : 𝚺ᴬ₁-Relation (ModelRewrite (M := M)) := by
  have group (es : List Templates.Equation) :
      𝚺ᴬ₁-Relation (fun a b : M => ∃ e ∈ es, modelInstance e a b) := by
    induction es with
    | nil => simp [List.not_mem_nil]
    | cons e rest ih =>
      have head := modelInstance_definable (M := M) e
      have expand : (fun a b : M => ∃ x ∈ e :: rest, modelInstance x a b) =
          fun a b => modelInstance e a b ∨ ∃ x ∈ rest, modelInstance x a b := by
        funext a b
        apply propext
        constructor
        · rintro ⟨x,listed,val⟩
          rcases List.mem_cons.mp listed with rfl | member
          · exact Or.inl val
          · exact Or.inr ⟨x,member,val⟩
        · rintro (value | ⟨x,h,value⟩)
          · exact ⟨e,List.mem_cons_self,value⟩
          · exact ⟨x,List.mem_cons_of_mem _ h,value⟩
      rw [expand]
      definability
  exact group equations

theorem modelRewrite_symm {s t : M} (run : ModelRewrite s t) : ModelRewrite t s := by
  obtain ⟨e,inTable,v,p,q,good,direction⟩ := run
  exact ⟨e,inTable,v,p,q,good,direction.elim (fun h => .inr h.symm) (fun h => .inl h.symm)⟩

theorem modelRewrite_context {s t : M} (run : ModelRewrite s t) (front rest : M) :
    ModelRewrite (contextWord front s rest) (contextWord front t rest) := by
  obtain ⟨e,inTable,v,p,q,good,direction⟩ := run
  refine ⟨e,inTable,v,appendVector front p,appendVector q rest,good,?_⟩
  simp only [modelMatch] at direction
  simp only [modelMatch]
  rcases direction with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply Or.inl
    simp [contextWord,appendVector_assoc]
  · apply Or.inr
    simp [contextWord,appendVector_assoc]

def ModelDerives (old new : M) : Prop := ∃ n : M, Chain ModelRewrite n old new

theorem modelDerives_definable : 𝚺ᴬ₁-Relation (ModelDerives (M := M)) := by
  have step := modelRewrite_definable (M := M)
  unfold ModelDerives Chain
  definability

theorem ModelDerives.refl (s : M) : ModelDerives s s := ⟨0,Chain.refl _ _⟩

theorem ModelDerives.single {s t : M} (step : ModelRewrite s t) : ModelDerives s t :=
  ⟨1,Chain.single step⟩

theorem ModelDerives.trans {s t u : M} (first : ModelDerives s t) (last : ModelDerives t u) :
    ModelDerives s u := by
  obtain ⟨n,path⟩ := first
  obtain ⟨m,rest⟩ := last
  exact ⟨n+m,path.trans rest⟩

theorem ModelDerives.symm {s t : M} (run : ModelDerives s t) : ModelDerives t s := by
  obtain ⟨n,trace⟩ := run
  exact ⟨n,trace.reverse (fun _ _ => modelRewrite_symm)⟩

theorem ModelDerives.context {s t : M} (run : ModelDerives s t) (front rest : M) :
    ModelDerives (contextWord front s rest) (contextWord front t rest) := by
  obtain ⟨n,trace⟩ := run
  let translate := fun v : M => contextWord front v rest
  have graph : 𝚺ᴬ₁-Function₁ translate := by unfold translate contextWord; definability
  exact ⟨n,Chain.map trace translate graph (fun _ _ step => modelRewrite_context step front rest)⟩

end PalomarI3334.SearchProgram
