module
public import I0451.ArithmeticProofCompiler

/-! Arithmetical derivations in the literal proof calculus.
A derivation is a model-coded sequence of formulas with each line
justified by one of the native rules. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wordRunsTo_defined : 𝚺ᴬ₁-Relation₃[V] (WordRunsTo : V → V → V → Prop) := by
  have update := wordStep_binary_defined (V := V)
  have test : 𝚺ᴬ₁-Relation₃[V] (fun (word initial result : V) => ∃ history : V,
    Seq history ∧ lh history = lh word + 1 ∧ znth history 0 = ⟪0, initial⟫ ∧
    (∀ j < lh word, znth history (j + 1) = wordStep word (znth history j)) ∧
    π₂ (znth history (lh word)) = result) := by definability
  change 𝚺ᴬ₁.Definable (V := V) (fun v : Fin 3 → V => WordRunsTo (v 0) (v 1) (v 2))
  exact test.of_iff fun _ =>
    ⟨fun ⟨history, ran, result⟩ => ⟨history, ran.sequence, ran.size, ran.begins, ran.advances, result⟩,
     fun ⟨history, seq, size, begins, advances, result⟩ => ⟨history, ⟨seq, size, begins, advances⟩, result⟩⟩

private theorem neutralCode_defined :
    𝚺ᴬ₁-Function₁[V] (fun tail => packModelStore (neutralStore tail)) := by
  change 𝚺ᴬ₁-Function₁[V] (fun tail : V => ⟪0, 0, tail, 0, 0, 0⟫ + 1)
  definability

theorem compiledPushes_defined : 𝚺ᴬ_[3]-Predicate[V] (CompiledPushes : V → Prop) := by
  let Runs (v : Fin 2 → V) (tail : V) :=
    WordRunsTo (v 0) (packModelStore (neutralStore tail)) 0 ∨
    WordRunsTo (v 0) (packModelStore (neutralStore tail)) (packModelStore (neutralStore (cantor (v 1) tail)))
  let encode (tail : V) := packModelStore (neutralStore tail)
  let : 𝚺ᴬ₁-Function₁[V] encode := neutralCode_defined
  have execution := wordRunsTo_defined (V := V)
  have single : 𝚺ᴬ₁.Definable (V := V) (fun v : Fin 3 → V => Runs (v ·.succ) (v 0)) := by
    have tailIn : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 3 → V => encode (v 0)) :=
      Bounding.HierarchySymbol.DefinableFunction₁.comp (by definability)
    have tailOut : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 3 → V => encode (cantor (v 2) (v 0))) :=
      Bounding.HierarchySymbol.DefinableFunction₁.comp (by definability)
    have word : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 3 → V => v 1) := by definability
    have stopped := Bounding.HierarchySymbol.DefinableRel₃.comp execution word tailIn
      (Bounding.HierarchySymbol.DefinableFunction.const 0)
    have advanced := Bounding.HierarchySymbol.DefinableRel₃.comp execution word tailIn tailOut
    exact Bounding.HierarchySymbol.Definable.or stopped advanced
  have arbitraryTail : 𝚷ᴬ_[2].Definable (V := V) (fun v : Fin 2 → V => ∀ tail, Runs v tail) :=
    Bounding.HierarchySymbol.Definable.all (single.of_lt (by decide))
  have larger : 𝚺ᴬ_[3].Definable (V := V) (fun v : Fin 2 → V => ∀ tail, Runs v tail) :=
    arbitraryTail.of_lt (by decide)
  apply Bounding.HierarchySymbol.Definable.exs
  exact Bounding.HierarchySymbol.Definable.and (by definability) larger

inductive NativeLine (book : V) (line : V) : V → Prop where
  | truth : NativeLine book line 0
  | foundation : NativeLine book line (literalFoundationCode : V)
  | berkeley : NativeLine book line (literalBerkeleyCode : V)
  | head (a b c x f : V) (member : f ∈ modelEncoding.heads a b c x) : NativeLine book line f
  | bundle (a b c : V) (left : c ≠ a) (right : c ≠ b) : NativeLine book line (modelEncoding.bundle a b c)
  | generalize (label prior : V) (earlier : prior < line) :
      NativeLine book line (modelEncoding.all label (znth book prior))
  | detach (a b i j : V) (first : i < line) (second : j < line)
      (antecedent : znth book i = a) (conditional : znth book j = modelImp a b) :
      NativeLine book line b

def NativeProof (book f : V) : Prop :=
  Seq book ∧ (∃ i < lh book, znth book i = f) ∧ ∀ i < lh book, NativeLine book i (znth book i)

theorem NativeLine.compiles {book line formula : V} (step : NativeLine book line formula)
    (earlier : ∀ j < line, CompiledPushes (znth book j)) :
    CompiledPushes formula := by
  cases step with
  | truth => exact compiled_truth
  | foundation => exact compiled_foundation
  | berkeley => exact compiled_berkeley
  | head a b c x f member => exact compiled_head member
  | bundle a b c first second => exact compiled_bundle first second
  | generalize label prior before => exact (earlier prior before).generalize label
  | detach a b i j first second antecedent conditional =>
    exact (antecedent ▸ earlier i first).detach (conditional ▸ earlier j second)

theorem NativeProof.compiles [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] {book f : V} (proof : NativeProof book f) :
    CompiledPushes f := by
  obtain ⟨_, ⟨position, inside, rfl⟩, lines⟩ := proof
  have formula : 𝚺ᴬ_[3]-Predicate[V] (fun i => i < lh book → CompiledPushes (znth book i)) := by
    have compiler := compiledPushes_defined (V := V)
    definability
  have each := InductionOnHierarchy.order_induction 𝚺 3 formula (by
    intro i prior inside
    apply (lines i inside).compiles
    exact fun j before => prior j before (lt_trans before inside))
  exact each position inside

theorem literal_halts_of_native_refutation [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] {book : V} (proof : NativeProof book 1) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) :=
  literal_halts_of_compiled_contradiction proof.compiles

end I0451.Arithmetization
