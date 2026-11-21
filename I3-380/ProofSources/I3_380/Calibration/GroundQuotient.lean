module
public import I3_380.Calibration.GroundCongruence
public import I3_380.Search.Compiler.SourceEquations
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem application_congr {n : Nat} (symbol : FunctionSymbol n)
    {a b : Fin n → GroundTerm M} (agree : ∀ i, groundSetoid.r (a i) (b i)) :
    groundSetoid.r (application symbol a) (application symbol b) := by
  let replace := fun (k : Nat) (i : Fin n) => if i.val < k then b i else a i
  have zero : replace 0 = a := by funext i; simp [replace]
  have final : replace n = b := by funext i; simp [replace,i.isLt]
  have through (k : Nat) (bound : k ≤ n) :
      groundSetoid.r (application symbol a) (application symbol (replace k)) := by
    induction k with
    | zero => rw [zero]
    | succ k ih =>
      let j : Fin n := ⟨k,by omega⟩
      have original : replace k j = a j := by simp [replace,j]
      have following : Function.update (replace k) j (b j) = replace (k+1) := by
        funext i
        by_cases same : i = j
        · subst i
          simp [replace,j]
        · have diff : i.val ≠ k := by intro eq; exact same (Fin.ext eq)
          have relation : i.val < k+1 ↔ i.val < k := by omega
          simp [Function.update_of_ne same,replace,relation]
      have h := application_congr_argument symbol (replace k) j (agree j)
      have unchanged : Function.update (replace k) j (a j) = replace k := by
        rw [← original,Function.update_eq_self]
      rw [unchanged,following] at h
      exact groundSetoid.trans (ih (by omega)) h
  exact final ▸ through n le_rfl

abbrev GroundClasses (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  Quotient (groundSetoid (M := M))

def groundClass (t : GroundTerm M) : GroundClasses M := Quotient.mk groundSetoid t

noncomputable def representative (x : GroundClasses M) : GroundTerm M :=
  Classical.choose (Quotient.exists_rep x)

theorem groundClass_representative (x : GroundClasses M) : groundClass (representative x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

noncomputable def quotientApplication {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundClasses M) :
    GroundClasses M :=
  groundClass (application symbol (representative ∘ args))

theorem quotientApplication_class {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M) :
    quotientApplication symbol (groundClass ∘ args) = groundClass (application symbol args) := by
  apply Quotient.sound
  apply application_congr
  intro i
  exact Quotient.exact (groundClass_representative (groundClass (args i)))

noncomputable def quotientAlgebra : Algebra (GroundClasses M) where
  constant c := quotientApplication (.constant c) ![]
  neg x := quotientApplication .complement ![x]
  converse x := quotientApplication .converse ![x]
  choice x := quotientApplication .choose ![x]
  localRel x := quotientApplication .localRelation ![x]
  nand x y := quotientApplication .nand ![x,y]
  product x y := quotientApplication .product ![x,y]
  node x y z := quotientApplication .node ![x,y,z]

private theorem application_map {n : Nat} (symbol : FunctionSymbol n) (args : Fin n → GroundTerm M) :
    groundClass (application symbol args) = quotientApplication symbol (groundClass ∘ args) :=
  (quotientApplication_class symbol args).symm

theorem eval_quotient {V : Type} (args : V → GroundTerm M) (t : PalomarI3380.Term V) :
    quotientAlgebra.eval (groundClass ∘ args) t = groundClass (groundAlgebra.eval args t) := by
  induction t <;> simp only [Algebra.eval,Function.comp_apply, *] <;> try rfl
  all_goals
    simp [quotientAlgebra,groundAlgebra,application_map,
      Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton]

theorem quotientAlgebra_models_rows : (quotientAlgebra (M := M)).Models Compiler.Source.rows := by
  intro e he values
  have representatives : groundClass ∘ (representative ∘ values) = values :=
    funext fun i => groundClass_representative (values i)
  change quotientAlgebra.eval values e.1 = quotientAlgebra.eval values e.2
  rw [← representatives,eval_quotient,eval_quotient]
  exact Quotient.sound (equation_congr he (representative ∘ values))

theorem quotientAlgebra_preceding :
    ((quotientAlgebra (M := M)).withStages).Models Manifest.preceding :=
  ((quotientAlgebra (M := M)).models_final_iff).mp
    ((Compiler.Source.source_models_iff _).mp quotientAlgebra_models_rows)

end PalomarI3380.Calibration.TermWords
