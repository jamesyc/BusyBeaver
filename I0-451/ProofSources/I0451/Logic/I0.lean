module
public import I0451.Logic.CodedElementarity
public import I0451.Logic.RankCollection
public import I0451.Logic.RelativeConstructible

/-! First-order presentation of I₀ by the ultrapower of L(V_{λ+1}).
A local collapse represents a value of the class ultrapower by a set
of representatives closed under predecessors modulo the measure.
The constant-function map is checked on set stages of L(V_{λ+1}).

The proper-ultrapower presentation follows Schlutzenberg,
"On the consistency of ZF with an elementary embedding from
V_{λ+2} into V_{λ+2}", Definition 2.7 and Proposition 3.5. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.SetAssignments I0451.Logic.ZFModel

/-- An even ordinal has an even finite tail after zero or a limit. -/
def evenOrdinalDef : SetTheorySemisentence 1 :=
  f“lambda. !IsOrdinal.dfn lambda ∧ ∃ w n chain zero base,
    !isω w ∧ n ∈ w ∧ !isEmpty zero ∧ :Seq chain ∧
    !lh.dfn (!succ.dfn n) chain ∧ !znth.dfn base chain zero ∧
    !znth.dfn lambda chain n ∧ !IsOrdinal.dfn base ∧
    (∀ a ∈ base, ∃ b ∈ base, a ∈ b) ∧
    ∀ i ∈ n, ∃ a b,
      !znth.dfn a chain i ∧ !znth.dfn b chain (!succ.dfn i) ∧ !succ.dfn b (!succ.dfn a)”

/-- A proper ultrafilter on the subsets of X that belong to L(X). -/
def constructibleUltrafilterDef : SetTheorySemisentence 2 :=
  “X U. X ∈ U ∧ (∀ A ∈ U, A ⊆ X ∧ !relativeConstructibleDef X A ∧ ¬!isEmpty A) ∧
    (∀ A ∈ U, ∀ B ∈ U, ∃ C ∈ U, C ⊆ A ∧ C ⊆ B) ∧
    (∀ A ∈ U, ∀ B, A ⊆ B → B ⊆ X → !relativeConstructibleDef X B → B ∈ U) ∧
    ∀ A, A ⊆ X → !relativeConstructibleDef X A →
      (A ∈ U ∨ ∃ B ∈ U, ∀ t ∈ X, t ∈ B ↔ t ∉ A)”

def constructibleFunctionDef : SetTheorySemisentence 2 :=
  “X f. !relativeConstructibleDef X f ∧ ∃ values,
    !range.dfn values f ∧ !function.dfn f values X ∧ ∀ y ∈ values, !relativeConstructibleDef X y”

def ultrapowerEqDef : SetTheorySemisentence 3 :=
  “U f g. ∃ A ∈ U, ∀ t ∈ A, ∃ y, !atDef f t y ∧ !atDef g t y”

def ultrapowerMemDef : SetTheorySemisentence 3 :=
  “U f g. ∃ A ∈ U, ∀ t ∈ A, ∃ x y, !atDef f t x ∧ !atDef g t y ∧ x ∈ y”

def ultrapowerValueDef : SetTheorySemisentence 4 :=
  “X U f y. ∃ representatives values collapse,
    f ∈ representatives ∧ !atDef collapse f y ∧ !IsTransitive.dfn values ∧
    !function.dfn collapse values representatives ∧ !range.dfn values collapse ∧
    (∀ g ∈ representatives, !constructibleFunctionDef X g) ∧
    (∀ g ∈ representatives, ∀ h ∈ representatives, ∀ u v,
      !atDef collapse g u → !atDef collapse h v →
        ((u = v ↔ !ultrapowerEqDef U g h) ∧ (u ∈ v ↔ !ultrapowerMemDef U g h))) ∧
    ∀ g ∈ representatives, ∀ h, !constructibleFunctionDef X h → !ultrapowerMemDef U h g →
      ∃ representative ∈ representatives, !ultrapowerEqDef U h representative”

/-- The quotient by equality modulo the measure collapses onto L(X). -/
def realizesUltrapowerDef : SetTheorySemisentence 2 :=
  “X U.
    (∀ f, !constructibleFunctionDef X f → ∃! y, !relativeConstructibleDef X y ∧ !ultrapowerValueDef X U f y) ∧
    (∀ y, !relativeConstructibleDef X y → ∃ f, !constructibleFunctionDef X f ∧ !ultrapowerValueDef X U f y) ∧
    ∀ f g, !constructibleFunctionDef X f → !constructibleFunctionDef X g → ∀ y z,
      !ultrapowerValueDef X U f y → !ultrapowerValueDef X U g z →
        (!relativeConstructibleDef X y ∧ !relativeConstructibleDef X z ∧
          (y = z ↔ !ultrapowerEqDef U f g) ∧ (y ∈ z ↔ !ultrapowerMemDef U f g))”

def ultrapowerEmbeddingDef : SetTheorySemisentence 4 :=
  “X U x y. !relativeConstructibleDef X x ∧ ∃ f, !constructibleFunctionDef X f ∧
    (∀ t ∈ X, !atDef f t x) ∧ !ultrapowerValueDef X U f y”

def ultrapowerRestrictionDef : SetTheorySemisentence 5 :=
  “X U source target graph. !function.dfn graph target source ∧
    ∀ x ∈ source, ∀ y, !atDef graph x y ↔ !ultrapowerEmbeddingDef X U x y”

def elementaryOnConstructibleStagesDef : SetTheorySemisentence 2 :=
  “X U. ∀ a, !IsOrdinal.dfn a → ∃ b source target graph,
    !IsOrdinal.dfn b ∧ !ultrapowerEmbeddingDef X U a b ∧
    !relativeConstructibleStageDef source X a ∧ !relativeConstructibleStageDef target X b ∧
    !ultrapowerEmbeddingDef X U source target ∧ !ultrapowerRestrictionDef X U source target graph ∧ !preservesSatisfactionDef source target graph”

/-- The proper embedding is recovered from its measure on V_{λ+1}.
The restriction to V_λ belongs to L(V_{λ+1}). -/
def i0SetAxiom : SetTheorySentence :=
  f“∃ lambda kappa lower X U graph,
    !evenOrdinalDef lambda ∧ !IsOrdinal.dfn kappa ∧ kappa ∈ lambda ∧
    !cumulativeLevelDef lower lambda ∧ !cumulativeLevelDef X (!succ.dfn lambda) ∧
    !constructibleUltrafilterDef X U ∧ !realizesUltrapowerDef X U ∧
    !ultrapowerEmbeddingDef X U X X ∧ !ultrapowerEmbeddingDef X U lambda lambda ∧
    ¬!ultrapowerEmbeddingDef X U kappa kappa ∧
    (∀ a ∈ kappa, !ultrapowerEmbeddingDef X U a a) ∧
    !ultrapowerRestrictionDef X U lower lower graph ∧ !relativeConstructibleDef X graph ∧
    !elementaryOnConstructibleStagesDef X U”

def zfI0 : SetTheory := 𝗭𝗙 ∪ {i0SetAxiom}

def zfcI0 : SetTheory := 𝗭𝗙𝗖 ∪ {i0SetAxiom}

instance : 𝗭𝗙 ⪯ zfI0 :=
  Entailment.WeakerThan.ofSubset fun _ h => Or.inl h

instance : 𝗭𝗙 ⪯ zfcI0 :=
  Entailment.WeakerThan.ofSubset fun _ h => Or.inl (Or.inl h)

instance : zfI0 ⪯ zfcI0 :=
  Entailment.WeakerThan.ofSubset (Set.union_subset_union_left _ Set.subset_union_left)

end I0451.Logic
