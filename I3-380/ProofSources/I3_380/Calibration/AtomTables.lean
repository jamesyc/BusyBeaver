module
public import I3_380.Calibration.FilterSets
public import I3_380.Calibration.FilterSatisfiability
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def atomEntry {arity : Nat} (symbol : GraphSymbol arity) (args : M) : M :=
  ⟪(arity : M),(⌜(show GraphLanguage.Rel arity from symbol)⌝ : M),args⟫

theorem atomEntry_injective {a b : Σ arity, GraphSymbol arity} {v w : M}
    (eq : atomEntry a.2 v = atomEntry b.2 w) : a=b ∧ v=w := by
  have arityCode : (a.1 : M) = (b.1 : M) := by
    simpa [atomEntry] using congrArg (fun x : M => π₁ x) eq
  have arity : a.1=b.1 := Nat.cast_inj.mp arityCode
  rcases a with ⟨a,s⟩
  rcases b with ⟨b,t⟩
  change a=b at arity
  subst b
  have numbers : (⌜(show GraphLanguage.Rel a from s)⌝ : M) =
      ⌜(show GraphLanguage.Rel a from t)⌝ := by
    simpa [atomEntry] using congrArg (fun x : M => π₁ (π₂ x)) eq
  have values : v=w := by simpa [atomEntry] using congrArg (fun x : M => π₂ (π₂ x)) eq
  have same : s=t := by
    apply (Encodable.encode_injective (α := GraphLanguage.Rel a))
    exact Nat.cast_inj.mp numbers
  exact ⟨by rw [same],values⟩

def atomTest (seed : CanonicalTerm M) : {arity : Nat} → GraphSymbol arity → M → Prop
  | _, .relation .chosen, args => ChosenCode seed args.[0]
  | _, .relation .equal, args => args.[0] = args.[1]
  | _, .operation op, args => (operationGraphDef op).val.Evalb ![args]

theorem atomTest_definable (seed : CanonicalTerm M) {arity : Nat} (symbol : GraphSymbol arity) :
    𝚺ᴬ_[2]-Predicate (atomTest seed symbol) := by
  cases symbol with
  | relation symbol =>
    cases symbol with
    | chosen =>
      have membership := chosenCode_definable seed
      change 𝚺ᴬ_[2].Definable (fun v : Fin 1 → M => ChosenCode seed (v 0).[0])
      apply membership.comp
      definability
    | equal =>
      change 𝚺ᴬ_[2].Definable (fun v : Fin 1 → M => (v 0).[0]=(v 0).[1])
      definability
  | operation f =>
    let P (args : M) := (operationGraphDef f).val.Evalb ![args]
    have lookup : 𝚺ᴬ₁-Predicate P :=
      (show 𝚺ᴬ₁-Predicate P via operationGraphDef f from
        .mk fun v => by
          change (operationGraphDef f).val.Evalb v ↔ (operationGraphDef f).val.Evalb ![v 0]
          rw [← Matrix.fun_eq_vec_one v]).to_definable
    exact lookup.of_lt (by decide)

def taggedTests (symbols : List (Σ arity, GraphSymbol arity)) (seed : CanonicalTerm M) (entry : M) : Prop :=
  ∃ symbol ∈ symbols, ∃ args, entry = atomEntry symbol.2 args ∧ atomTest seed symbol.2 args

theorem taggedTests_definable (symbols : List (Σ arity, GraphSymbol arity)) (seed : CanonicalTerm M) :
    𝚺ᴬ_[2]-Predicate (taggedTests symbols seed) := by
  apply Bounding.HierarchySymbol.Definable.disj₂ symbols
  intro symbol
  have test := atomTest_definable seed symbol.2
  dsimp only [atomEntry]
  definability

def listedGraphSymbols : List (Σ arity, GraphSymbol arity) :=
  (List.range 5).flatMap fun arity => (graphSymbols arity).map (Sigma.mk arity)

theorem listedGraphSymbols_complete (s : Σ arity, GraphSymbol arity) : s ∈ listedGraphSymbols := by
  rcases s with ⟨arity,symbol⟩
  have bound : arity < 5 := by
    cases symbol with
    | relation r => cases r <;> decide
    | operation f => cases f <;> decide
  exact List.mem_flatMap.mpr ⟨arity,List.mem_range.mpr bound,List.mem_map.mpr ⟨symbol,graphSymbols_complete _,rfl⟩⟩

theorem taggedTests_at (seed : CanonicalTerm M) {arity : Nat} (symbol : GraphSymbol arity) (args : M) :
    taggedTests listedGraphSymbols seed (atomEntry symbol args) ↔ atomTest seed symbol args := by
  constructor
  · rintro ⟨other,_,entry,eq,h⟩
    have same := atomEntry_injective (a := ⟨arity,symbol⟩) (b := other) eq
    obtain ⟨rfl,rfl⟩ := same
    exact h
  · exact fun h => ⟨⟨arity,symbol⟩,listedGraphSymbols_complete _,args,rfl,h⟩

variable {V : Type} {E G : V → V → Prop}
    {laws : Logic.Expanded.ClassAxioms E G} {inhabited : Nonempty V}
    (D : Logic.Expanded.OmegaDomain laws inhabited)

theorem atoms_set :
    letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
    ∀ seed : CanonicalTerm D.Points, ∃ table : V, ∀ {arity : Nat} (s : GraphSymbol arity) (args : D.Points),
      E (atomEntry s args).val table ↔ atomTest seed s args := by
  letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
  intro seed
  obtain ⟨formula,meaning⟩ := (taggedTests_definable listedGraphSymbols seed).definable
  obtain ⟨table,spec⟩ := D.separate_arithmetic formula.val id
  refine ⟨table,fun s args => (spec _).trans (Iff.trans ?_ (taggedTests_at seed s args))⟩
  constructor
  · rintro ⟨x,represents,holds⟩
    have same : x=atomEntry s args := Subtype.ext represents
    subst x
    exact (meaning ![atomEntry s args]).mp holds
  · intro h
    exact ⟨atomEntry s args,rfl,(meaning ![atomEntry s args]).mpr h⟩

end PalomarI3380.Calibration.TermWords
