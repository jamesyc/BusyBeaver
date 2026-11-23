module
public import I3_334.Calibration.LegacyValues
public import I3_334.Calibration.ModelFold
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Calibration (FilterLanguage FunctionSymbol functions functions_complete functions_distinct)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def stackTail (s : M) : M := π₂ (s-1)

@[simp] theorem stackTail_cons (head tail : M) : stackTail (head ∷ tail) = tail := by
  simp [stackTail,adjoin_def,Arithmetic.add_sub_self]

set_option maxHeartbeats 800000 in
theorem legacyApplication_definable {n : Nat} (f : FunctionSymbol n) :
    𝚺ᴬ_[2]-Function₁ (fun s : M => legacyApplication f (fun i => s.[(i.val : M)])) := by
  have localDef := legacyLocal_definable (M := M)
  have nodeDef := legacyNode_definable (M := M)
  have negDef : 𝚺ᴬ_[2]-Function₁ (legacyUnary (M := M) 3) := (legacyUnary_definable 3).of_lt (by decide)
  have convDef : 𝚺ᴬ_[2]-Function₁ (legacyUnary (M := M) 4) := (legacyUnary_definable 4).of_lt (by decide)
  have choiceDef : 𝚺ᴬ_[2]-Function₁ (legacyUnary (M := M) 1) := (legacyUnary_definable 1).of_lt (by decide)
  have nandDef : 𝚺ᴬ_[2]-Function₂ (legacyBinary (M := M) 3) := (legacyBinary_definable 3).of_lt (by decide)
  have prodDef : 𝚺ᴬ_[2]-Function₂ (legacyBinary (M := M) 4) := (legacyBinary_definable 4).of_lt (by decide)
  have meetDef : 𝚺ᴬ_[2]-Function₂ (legacyMeet (M := M)) := legacyMeet_definable.of_lt (by decide)
  cases f <;> change 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = _) <;>
    simp only [legacyApplication,legacyComplement,legacyConverse,legacyChoice,legacyNand,legacyProduct,
      legacyCodedLocal,legacyCodedNode]
  case node =>
    have gn : 𝚺ᴬ_[2].DefinableFunction
        (fun v : Fin 1 → M => legacyNode (v 0).[0] (v 0).[1] (v 0).[2]) := by
      apply Bounding.HierarchySymbol.DefinableFunction₃.comp (F := legacyNode)
      all_goals definability
    have effect : 𝚺ᴬ_[2]-Function₁ (fun s : M => ⟪legacyNode s.[0] s.[1] s.[2],0⟫) :=
      Bounding.HierarchySymbol.DefinableFunction₂.comp (F := pair) (Γ := 𝚺) gn (.const 0)
    simpa only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,Fin.val_zero,Fin.val_one,Fin.val_two] using effect
  all_goals definability

noncomputable def popStack : Nat → M → M
  | 0, s => s
  | n+1, s => popStack n (stackTail s)

theorem popStack_definable (n : Nat) : 𝚺ᴬ_[2]-Function₁ (popStack (M := M) n) := by
  have tailDef : 𝚺ᴬ_[2]-Function₁ (stackTail (M := M)) := by
    change 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = stackTail (v 1))
    unfold stackTail
    definability
  induction n with
  | zero => change 𝚺ᴬ_[2]-Function₁ (fun s : M => s); definability
  | succ n ih =>
    exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := popStack n) tailDef

noncomputable def legacyStackApply {n : Nat} (f : FunctionSymbol n) (s : M) : M :=
  if (n : M) ≤ len s then legacyApplication f (fun i => s.[(i.val : M)]) ∷ popStack n s
  else legacyConstant .D ∷ s

theorem legacyStackApply_definable {n : Nat} (f : FunctionSymbol n) :
    𝚺ᴬ_[2]-Function₁ (legacyStackApply (M := M) f) := by
  let apply := fun s : M => legacyApplication f (fun i => s.[(i.val : M)])
  have applyDef : 𝚺ᴬ_[2]-Function₁ apply := legacyApplication_definable f
  have popDef := popStack_definable (M := M) n
  letI : 𝚺ᴬ_[2]-Function₂ (adjoin : M → M → M) := adjoin_definable.of_zero
  have effect : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = apply (v 1) ∷ popStack n (v 1)) :=
    Bounding.HierarchySymbol.DefinableFunction₂.comp (F := adjoin) (Γ := 𝚺) applyDef popDef
  have read : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => (n : M) ≤ len (v 1)) := by definability
  have absent : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => len (v 1) < (n : M)) := by definability
  have fallback : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = legacyConstant .D ∷ v 1) := by definability
  refine ((read.and effect).or (absent.and fallback)).of_iff (fun v => ?_)
  by_cases limit : (n : M) ≤ len (v 1)
  · simp [legacyStackApply,limit,apply,not_lt_of_ge limit]
  · simp [legacyStackApply,limit,apply,lt_of_not_ge limit]

noncomputable def oldToken {k : Nat} (f : FunctionSymbol k) : M :=
  ⟪(k : M),(⌜(show FilterLanguage.Func k from f)⌝ : M)⟫

def legacySymbols : List (Σ n, FunctionSymbol n) :=
  (List.range 4).flatMap fun n => (functions n).map (Sigma.mk n)

theorem legacySymbols_mem {n : Nat} (f : FunctionSymbol n) : Sigma.mk n f ∈ legacySymbols := by
  have arity : n < 4 := by cases f <;> decide
  exact List.mem_flatMap.mpr ⟨n,List.mem_range.mpr arity,List.mem_map.mpr ⟨f,functions_complete f,rfl⟩⟩

theorem oldToken_injective :
    Function.Injective (fun f : Σ n, FunctionSymbol n => oldToken (M := M) f.2) := by
  rintro ⟨a,f⟩ ⟨b,g⟩ eq
  have sameArity : a = b := by
    have sizes := congrArg (fun x : M => π₁ x) eq
    simp only [oldToken,Arithmetic.pi₁_pair] at sizes
    exact_mod_cast sizes
  subst b
  have sameCode : (⌜(show FilterLanguage.Func a from f)⌝ : M) = ⌜(show FilterLanguage.Func a from g)⌝ := by
    have tags := congrArg (fun x : M => π₂ x) eq
    simpa only [oldToken,Arithmetic.pi₂_pair] using tags
  have equal : f = g := (quote_func_inj (L := FilterLanguage) (V := M) f g).mp sameCode
  subst g
  rfl

noncomputable def legacySelect : List (Σ n, FunctionSymbol n) → M → M → M
  | [], _, stack => legacyConstant .D ∷ stack
  | f :: fs, token, stack =>
    if token = oldToken f.2 then legacyStackApply f.2 stack else legacySelect fs token stack

theorem legacySelect_at {n : Nat} (f : FunctionSymbol n) (symbols : List (Σ n, FunctionSymbol n))
    (listed : Sigma.mk n f ∈ symbols) (stack : M) :
    legacySelect symbols (oldToken f) stack = legacyStackApply f stack := by
  induction symbols with
  | nil => simp at listed
  | cons head rest ih =>
    by_cases eq : oldToken (M := M) f = oldToken head.2
    · have same := oldToken_injective (M := M) (a₁ := Sigma.mk n f) (a₂ := head) eq
      subst head
      simp [legacySelect]
    · have tail : Sigma.mk n f ∈ rest := (List.mem_cons.mp listed).resolve_left
        (fun same => eq (congrArg (fun r => oldToken r.2) same))
      simp [legacySelect,eq,ih tail]

theorem legacySelect_definable (symbols : List (Σ n, FunctionSymbol n)) :
    𝚺ᴬ_[2]-Function₂ (legacySelect (M := M) symbols) := by
  induction symbols with
  | nil => change 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M =>
      v 0 = (legacyConstant .D ∷ v 2)); definability
  | cons f rest ih =>
    have on : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = legacyStackApply f.2 (v 1)) :=
      legacyStackApply_definable f.2
    let p := fun v : Fin 3 → M => v 1 = oldToken f.2
    have positive : 𝚺ᴬ_[2].Definable p := by unfold p; definability
    have negative : 𝚺ᴬ_[2].Definable (fun v => ¬p v) := by unfold p; definability
    have fallback : 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M => v 0 = legacySelect rest (v 1) (v 2)) := ih
    have graph := (positive.and (on.retraction (![0,2] : Fin 2 → Fin 3))).or (negative.and fallback)
    refine graph.of_iff (fun v => ?_)
    by_cases eq : v 1 = (oldToken f.2 : M) <;> simp [p,legacySelect,eq]

noncomputable def legacyFold (word stack : M) : M :=
  modelFold (legacySelect legacySymbols) (legacySelect_definable legacySymbols) word stack

theorem legacyFold_definable : 𝚺ᴬ_[2]-Function₂ (legacyFold (M := M)) :=
  modelFold_definable (legacySelect_definable legacySymbols)

@[simp] theorem legacyFold_nil (stack : M) : legacyFold 0 stack = stack :=
  modelFold_nil _ _

theorem legacyFold_cons {n : Nat} (f : FunctionSymbol n) (word stack : M) :
    legacyFold (oldToken f ∷ word) stack = legacyStackApply f (legacyFold word stack) := by
  simp only [legacyFold,modelFold_adjoin,legacySelect_at f legacySymbols (legacySymbols_mem f)]

theorem legacyFold_append (a b stack : M) :
    legacyFold (PalomarI3380.ArithmeticMachine.SourceWords.appendVector a b) stack =
      legacyFold a (legacyFold b stack) :=
  modelFold_append _ _ _ _

end PalomarI3334.SearchProgram
