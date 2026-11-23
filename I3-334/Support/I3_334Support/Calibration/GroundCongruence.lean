module
public import I3_334Support.Calibration.GroundRewrites
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem RewriteStep.symm {x y : M} (step : RewriteStep x y) : RewriteStep y x := by
  obtain ⟨row,member,args,wellFormed,ctx,match'⟩ := step
  refine ⟨row,member,args,wellFormed,ctx,?_⟩
  rcases match' with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact Or.inr ⟨hy,hx⟩
  · exact Or.inl ⟨hy,hx⟩

theorem RewriteStep.context {x y : M} (step : RewriteStep x y) (outer : Context M) :
    RewriteStep (outer.fill x) (outer.fill y) := by
  obtain ⟨row,member,args,wellFormed,inner,match'⟩ := step
  refine ⟨row,member,args,wellFormed,outer.compose inner,?_⟩
  simp only [Context.compose_fill]
  rcases match' with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact Or.inl ⟨congrArg outer.fill hx,congrArg outer.fill hy⟩
  · exact Or.inr ⟨congrArg outer.fill hx,congrArg outer.fill hy⟩

/-- Conversion of token vectors by an internally finite chain of released
rewrite steps. The trace is available as evidence for the scheduler. -/
def Convertible (x y : M) : Prop := ∃ n : M, Chain RewriteStep n x y

noncomputable def convertibleDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “a b. ∃ n, !(PalomarI3380.Arithmetic.chainDef (stepsDef Manifest.final)) n a b”

theorem convertibleDef_eval (a b : M) :
    convertibleDef.val.Evalb ![a,b] ↔ Convertible a b := by
  simp [convertibleDef,Convertible,PalomarI3380.Arithmetic.chainDef_eval rewriteStep_eval]

theorem Convertible.refl (x : M) : Convertible x x := ⟨0,Chain.refl _ x⟩

theorem Convertible.symm {x y : M} (path : Convertible x y) : Convertible y x := by
  obtain ⟨n,run⟩ := path
  exact ⟨n,run.reverse fun _ _ h => h.symm⟩

theorem Convertible.trans {x y z : M} (first : Convertible x y) (next : Convertible y z) :
    Convertible x z := by
  obtain ⟨n,first⟩ := first
  obtain ⟨k,next⟩ := next
  exact ⟨n+k,first.trans next⟩

theorem Convertible.context {x y : M} (path : Convertible x y) (c : Context M) :
    Convertible (c.fill x) (c.fill y) := by
  obtain ⟨n,run⟩ := path
  have definable : 𝚺ᴬ₁-Function₁ c.fill := by
    unfold Context.fill
    definability
  exact ⟨n,run.map c.fill definable (fun _ _ s => s.context c)⟩

def groundSetoid : Setoid (GroundTerm M) where
  r a b := Convertible (termTokens a.val) (termTokens b.val)
  iseqv := ⟨fun _ => Convertible.refl _,fun h => h.symm,fun h k => h.trans k⟩

theorem application_congr_argument {n : Nat} (symbol : FunctionSymbol n)
    (args : Fin n → GroundTerm M) (index : Fin n) {x y : GroundTerm M}
    (related : groundSetoid.r x y) :
    groundSetoid.r (application symbol (Function.update args index x))
      (application symbol (Function.update args index y)) := by
  obtain ⟨ctx,fill⟩ := application_context symbol args index
  change Convertible (termTokens (application symbol (Function.update args index x)).val)
    (termTokens (application symbol (Function.update args index y)).val)
  rw [fill,fill]
  exact Convertible.context related ctx

theorem equation_congr {row : Equation} (member : row ∈ Manifest.final)
    (args : Fin 3 → GroundTerm M) :
    groundSetoid.r (groundAlgebra.eval args row.1) (groundAlgebra.eval args row.2) := by
  change Convertible (termTokens (groundAlgebra.eval args row.1).val)
    (termTokens (groundAlgebra.eval args row.2).val)
  refine ⟨1,Chain.single ⟨row,member,matrixToVec (fun i => (args i).val),
    arguments_wellFormed args,⟨0,0⟩,Or.inl ?_⟩⟩
  simp only [Context.blank_fill,instantiate_eval, and_self]

end PalomarI3380.Calibration.TermWords
