module
public import I3_334.Calibration.ModelRewrite
public import I3_334.Proof.Recovery
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open ArithmeticMachine.SourceWords
open Templates (Pattern)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelSetoid (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Setoid M where
  r := ModelDerives
  iseqv := ⟨ModelDerives.refl,ModelDerives.symm,ModelDerives.trans⟩

abbrev ModelClass (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  Quotient (modelSetoid M)

def modelClass (t : M) : ModelClass M := Quotient.mk _ t

theorem modelClass_eq {a b : M} : modelClass a = modelClass b ↔ ModelDerives a b :=
  ⟨Quotient.exact,Quotient.sound (s := modelSetoid M)⟩

noncomputable def modelRep (t : ModelClass M) : M :=
  Classical.choose (Quotient.exists_rep t)

@[simp] theorem modelClass_rep (t : ModelClass M) : modelClass (modelRep t) = t :=
  Classical.choose_spec (Quotient.exists_rep t)

theorem joinVectors_append (a b : List M) :
    joinVectors (a ++ b) = appendVector (joinVectors a) (joinVectors b) := by
  induction a with
  | nil => simp [joinVectors]
  | cons x xs ih => simp [joinVectors,ih,appendVector_assoc]

theorem modelApplication_congr (tag : M) {a b : List M} (same : List.Forall₂ ModelDerives a b) :
    ModelDerives (modelApplication tag a) (modelApplication tag b) := by
  have length_eq := same.length_eq
  have joined : ∀ {a b : List M}, List.Forall₂ ModelDerives a b →
      ModelDerives (joinVectors a) (joinVectors b) := by
    intro a b related
    induction related with
    | nil => exact ModelDerives.refl _
    | @cons x y xs ys hd tl ih =>
      change ModelDerives (appendVector x (joinVectors xs)) (appendVector y (joinVectors ys))
      have left := hd.context 0 (joinVectors xs)
      have right := ih.context y 0
      simp only [contextWord,appendVector_nil,appendVector_empty_suffix] at left right
      exact left.trans right
  unfold modelApplication
  rw [length_eq]
  have inner := (joined same).context (?[⟪(b.length : M),tag⟫]) 0
  simpa only [contextWord,appendVector_empty_suffix,appendVector_cons,appendVector_nil] using inner

noncomputable def quotientApply (tag : Nat) (args : List (ModelClass M)) : ModelClass M :=
  modelClass (modelApplication (tag : M) (args.map modelRep))

theorem quotientApply_class (tag : Nat) (args : List M) :
    quotientApply tag (args.map modelClass) = modelClass (modelApplication (tag : M) args) := by
  apply modelClass_eq.mpr
  apply modelApplication_congr
  induction args with
  | nil => exact .nil
  | cons h t ih =>
    exact .cons (modelClass_eq.mp (modelClass_rep (modelClass h))) ih

noncomputable def modelAlgebra : NativeAlgebra (ModelClass M) where
  domain := quotientApply 1 []
  embedding := quotientApply 0 []
  membership := quotientApply 2 []
  seed := quotientApply 3 []
  identity := quotientApply 5 []
  neg x := quotientApply 3 [x]
  converse x := quotientApply 4 [x]
  choice x := quotientApply 1 [x]
  nand x y := quotientApply 3 [x,y]
  product x y := quotientApply 4 [x,y]
  other := quotientApply

theorem modelAlgebra_operation (tag : Nat) (args : List (ModelClass M)) :
    (modelAlgebra (M := M)).operation tag args = quotientApply tag args := by
  unfold NativeAlgebra.operation
  split <;> rfl

def ModelSafe (x : ModelClass M) : Prop :=
  ∃ t : M, ClosedVector 3 t ∧ modelClass t = x

def ModelClosed (x : ModelClass M) : Prop :=
  ∃ t : M, ClosedVector 0 t ∧ modelClass t = x

theorem modelSafe_of_closed {a : M} (guard : ClosedVector 3 a) : ModelSafe (modelClass a) :=
  ⟨a,guard,rfl⟩

abbrev ClosedClass (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  {x : ModelClass M // ModelClosed x}

def closedClass (t : M) (good : ClosedVector 0 t) : ClosedClass M :=
  ⟨modelClass t,t,good,rfl⟩

noncomputable def closedRep (x : ClosedClass M) : M := Classical.choose x.property

theorem closedRep_valid (x : ClosedClass M) : ClosedVector 0 (closedRep x) :=
  (Classical.choose_spec x.property).1

@[simp] theorem closedRep_class (x : ClosedClass M) : modelClass (closedRep x) = x.val :=
  (Classical.choose_spec x.property).2

noncomputable def closedApply (tag : Nat) (args : List (ClosedClass M)) : ClosedClass M :=
  closedClass (modelApplication (tag : M) (args.map closedRep))
    (closed_application 0 _ _ (Arithmetic.zero_le _) (by
      intro w member
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
      exact closedRep_valid x))

theorem closedApply_value (tag : Nat) (args : List (ClosedClass M)) :
    (closedApply tag args).val = quotientApply tag (args.map Subtype.val) := by
  rw [show args.map Subtype.val = (args.map closedRep).map modelClass from by simp [List.map_map]]
  exact (quotientApply_class _ _).symm

noncomputable def modelClosedAlgebra : NativeAlgebra (ClosedClass M) where
  domain := closedApply 1 []
  embedding := closedApply 0 []
  membership := closedApply 2 []
  seed := closedApply 3 []
  identity := closedApply 5 []
  neg x := closedApply 3 [x]
  converse x := closedApply 4 [x]
  choice x := closedApply 1 [x]
  nand x y := closedApply 3 [x,y]
  product x y := closedApply 4 [x,y]
  other := closedApply

theorem closedAlgebra_operation (tag : Nat) (args : List (ClosedClass M)) :
    (modelClosedAlgebra (M := M)).operation tag args = closedApply tag args := by
  unfold NativeAlgebra.operation
  split <;> rfl

theorem closedAlgebra_eval (v : Fin 4 → ClosedClass M) (p : Pattern) :
    ((modelClosedAlgebra (M := M)).eval v p).val = (modelAlgebra (M := M)).eval (Subtype.val ∘ v) p := by
  induction p with
  | capture => rfl
  | constant => simp only [NativeAlgebra.eval,closedAlgebra_operation,modelAlgebra_operation,
      closedApply_value,List.map_nil]
  | unary _ _ ih => simp only [NativeAlgebra.eval,closedAlgebra_operation,modelAlgebra_operation,
      closedApply_value,List.map_cons,List.map_nil,ih]
  | binary _ _ _ ih₁ ih₂ => simp only [NativeAlgebra.eval,closedAlgebra_operation,modelAlgebra_operation,
      closedApply_value,List.map_cons,List.map_nil,ih₁,ih₂]

theorem modelAlgebra_eval (values : M) (p : Pattern) :
    (modelAlgebra (M := M)).eval (fun i => modelClass values.[(i.val : M)]) p =
      modelClass (modelTemplate values p) := by
  induction p with
  | capture => rfl
  | constant tag =>
    rw [NativeAlgebra.eval,modelAlgebra_operation,modelTemplate]
    exact quotientApply_class tag []
  | unary tag _ ih =>
    rw [NativeAlgebra.eval,modelAlgebra_operation,ih,modelTemplate]
    exact quotientApply_class tag [_]
  | binary tag _ _ ih₁ ih₂ =>
    rw [NativeAlgebra.eval,modelAlgebra_operation,ih₁,ih₂,modelTemplate]
    exact quotientApply_class tag [_,_]

theorem modelClosedAlgebra_models : (modelClosedAlgebra (M := M)).ModelsOn (ModelSafe ∘ Subtype.val) := by
  refine ⟨?_,?_⟩
  · intro eq listed a b c d safe
    obtain ⟨dWord,guard,hd⟩ := safe
    let values : M := ?[closedRep a,closedRep b,closedRep c,dWord]
    have third : (3 : M) = 2+1 := by
      exact_mod_cast (show (3 : Nat) = 2+1 by decide)
    have dEntry : values.[3] = dWord := by
      rw [third]
      simp only [values,nth_adjoin_succ,nth_adjoin_two,nth_adjoin_one,nth_adjoin_zero]
    have size : len values = 4 := by
      simp only [values,len_adjoin,len_nil,zero_add]
      exact_mod_cast (show (1 : Nat)+1+1+1 = 4 by decide)
    have typed : ModelSubstitution values :=
      ⟨size,by simpa [values] using closedRep_valid a,by simpa [values] using closedRep_valid b,
        by simpa [values] using closedRep_valid c,by rwa [dEntry]⟩
    have valuation : Subtype.val ∘ NativeAlgebra.valuation a b c d =
        (fun i : Fin 4 => modelClass values.[(i.val : M)]) := by
      funext i
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simp [NativeAlgebra.valuation,values]
      · simp [NativeAlgebra.valuation,values]
      · simp [NativeAlgebra.valuation,values]
      · change d.val = modelClass values.[3]
        rwa [dEntry,hd]
    apply Subtype.ext
    rw [closedAlgebra_eval,closedAlgebra_eval,valuation,modelAlgebra_eval,modelAlgebra_eval]
    apply modelClass_eq.mpr
    apply ModelDerives.single
    exact ⟨eq,listed,values,0,0,typed,Or.inl (by
      simp [modelMatch,contextWord])⟩
  · apply modelSafe_of_closed
    exact closed_application 3 3 [] le_rfl (by simp)

theorem modelSafe_closed_constructor {x y z : ClosedClass M}
    (sx : ModelSafe x.val) (sy : ModelSafe y.val) (sz : ModelSafe z.val) :
    let A := modelClosedAlgebra (M := M)
    ModelSafe (A.meet (A.product x (A.converse y)) (A.nand y z)).val := by
  obtain ⟨a,ha,ea⟩ := sx
  obtain ⟨b,hb,eb⟩ := sy
  obtain ⟨c,hc,ec⟩ := sz
  let conv := modelApplication (4 : M) [b]
  let prod := modelApplication (4 : M) [a,conv]
  let nand := modelApplication (3 : M) [b,c]
  let both := modelApplication (3 : M) [prod,nand]
  have vc : ClosedVector 3 conv := closed_application 3 4 [b]
    (by exact_mod_cast (show 3 ≤ (4 : Nat) by decide)) (by simpa using hb)
  have vp : ClosedVector 3 prod := closed_application 3 4 [a,conv]
    (by exact_mod_cast (show 3 ≤ (4 : Nat) by decide)) (by simpa using And.intro ha vc)
  have vn : ClosedVector 3 nand := closed_application 3 3 [b,c] le_rfl
    (by simpa using And.intro hb hc)
  have vb : ClosedVector 3 both := closed_application 3 3 [prod,nand] le_rfl
    (by simpa using And.intro vp vn)
  refine ⟨modelApplication 3 [both],closed_application 3 3 [both] le_rfl (by simpa using vb),?_⟩
  change modelClass (modelApplication 3 [both]) =
    (closedApply 3 [closedApply 3 [closedApply 4 [x,closedApply 4 [y]],closedApply 3 [y,z]]]).val
  simp only [closedApply_value,List.map_cons,List.map_nil,← ea,← eb,← ec]
  rw [show quotientApply 4 [modelClass b] = modelClass conv from quotientApply_class 4 [b],
    show quotientApply 4 [modelClass a, modelClass conv] = modelClass prod from
      quotientApply_class 4 [a,conv],
    show quotientApply 3 [modelClass b, modelClass c] = modelClass nand from
      quotientApply_class 3 [b,c],
    show quotientApply 3 [modelClass prod, modelClass nand] = modelClass both from
      quotientApply_class 3 [prod,nand]]
  exact (quotientApply_class 3 [both]).symm

end PalomarI3334.SearchProgram
