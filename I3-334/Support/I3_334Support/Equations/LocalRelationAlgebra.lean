module
public import I3_334Support.SetTheory.ClassModel
public import I3_334Support.SetTheory.Classes.ModelLocalEvaluation
public import I3_334Support.Search.Cantor
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop}

namespace ClassRelation

def diagonal (x : V) : ClassRelation E G :=
  ⟨fun a b => a = x ∧ b = x,
    ⟨.and (.eq (.variable 0) (.named x)) (.eq (.variable 1) (.named x)),
      by simp [Bound,Argument.bound], fun _ => Iff.rfl⟩⟩

def meet (r s : ClassRelation E G) : ClassRelation E G :=
  ⟨fun x y => r.holds x y ∧ s.holds x y,r.definable.intersection s.definable⟩

def rankDiagonal (stage : V) : ClassRelation E G :=
  ⟨fun a b => a = b ∧ E a stage,
    ⟨.and (.eq (.variable 0) (.variable 1)) (.mem (.variable 0) (.named stage)),
      by simp [Bound,Argument.bound], fun _ => Iff.rfl⟩⟩

end ClassRelation

/-- The relation constructor evaluates finite ternary trees with one
distinguished leaf. Class relations outside the tree encoding use the leaf. -/
inductive LocalTree where
  | leaf
  | node (r s t : LocalTree)

namespace LocalTree

def code : LocalTree → Nat
  | .leaf => 0
  | .node r s t => Cantor.pair r.code (Cantor.pair s.code t.code) + 1

theorem code_injective : Function.Injective code := by
  intro a
  induction a with
  | leaf =>
    intro b h
    cases b with
    | leaf => rfl
    | node r s t => simp [code] at h
  | node r s t ir is it =>
    intro b h
    cases b with
    | leaf => simp [code] at h
    | node r' s' t' =>
      have paired := congrArg Cantor.unpair (Nat.succ.inj h)
      rw [Cantor.unpair_pair,Cantor.unpair_pair] at paired
      have inside := congrArg (Cantor.unpair ∘ Prod.snd) paired
      simp only [Function.comp_apply,Cantor.unpair_pair] at inside
      rw [ir (congrArg Prod.fst paired),is (congrArg Prod.fst inside),it (congrArg Prod.snd inside)]

variable (N : SetContext (ClassRelation.algebra E G) V)

noncomputable def encode : LocalTree → ClassRelation E G
  | .leaf => .one
  | .node r s t => .diagonal (N.numeral (LocalTree.node r s t).code)

include N in
private theorem diagonal_ne_one (x : V) : ClassRelation.diagonal (E := E) (G := G) x ≠ .one := by
  intro eq
  have atPoint (y : V) : y = x := by
    have h : (ClassRelation.one (E := E) (G := G)).holds y y := rfl
    rw [← eq] at h
    exact h.1
  have absurd : (0 : Nat) = 1 :=
    N.numeral_injective ((atPoint (N.numeral 0)).trans (atPoint (N.numeral 1)).symm)
  omega

theorem encode_injective : Function.Injective (encode N) := by
  intro a b h
  cases a with
  | leaf =>
    cases b with
    | leaf => rfl
    | node r s t => exact (diagonal_ne_one N _ h.symm).elim
  | node r s t =>
    cases b with
    | leaf => exact (diagonal_ne_one N _ h).elim
    | node r' s' t' =>
      let n := N.numeral (LocalTree.node r s t).code
      have y : (encode N (.node r s t)).holds n n := ⟨rfl,rfl⟩
      rw [h] at y
      exact code_injective (N.numeral_injective y.1)

noncomputable def decode (r : ClassRelation E G) : LocalTree := by
  classical
  exact if h : ∃ t, encode N t = r then Classical.choose h else .leaf

theorem decode_encode (t : LocalTree) : decode N (encode N t) = t := by
  classical
  unfold decode
  rw [dite_eq_left (show ∃ u, encode N u = encode N t from ⟨t,rfl⟩)]
  exact encode_injective N (Classical.choose_spec (⟨t,rfl⟩ : ∃ u, encode N u = encode N t))

def relation (stage : V) : LocalTree → ClassRelation E G
  | .leaf => ClassRelation.member.product (ClassRelation.rankDiagonal stage)
  | .node r s t =>
    let middle := relation stage s
    ClassRelation.meet ((relation stage r).product middle.converse) (middle.nand (relation stage t))

theorem supported {stage : V} (closed : Internal.Transitive E stage) (t : LocalTree) {x y : V}
    (edge : (relation (E := E) (G := G) stage t).holds x y) : E x stage ∧ E y stage := by
  induction t generalizing x y with
  | leaf =>
    obtain ⟨z,hz,same,bound⟩ := edge
    subst z
    exact ⟨closed y bound x hz,bound⟩
  | node r s t ir is _ =>
    obtain ⟨⟨z,left,right⟩,_⟩ := edge
    exact ⟨(ir left).1,(is right).1⟩

def spare (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

private theorem spare_left (a b : Fin 3) : spare a b ≠ a := by
  unfold spare
  split <;> rename_i h0
  · exact Ne.symm h0.1
  split <;> rename_i h1
  · exact Ne.symm h1.1
  simp only [not_and,ne_eq,Decidable.not_not] at h0 h1
  intro eq
  subst a
  have first := h0 (by decide)
  have second := h1 (by decide)
  exact (by decide : (0 : Fin 3) ≠ 1) (first.symm.trans second)

private theorem spare_eq_swap (a b : Fin 3) : spare a b = spare b a := by
  simp only [spare,and_comm]

private theorem spare_right (a b : Fin 3) : spare a b ≠ b := by
  rw [spare_eq_swap]
  exact spare_left b a

def formula : LocalTree → Fin 3 → Fin 3 → LocalFormula
  | .leaf, a, b => .member a b
  | .node r s t, a, b =>
    let c := spare a b
    .conj (.bind c (.conj (formula r a c) (formula s b c)))
      (.neg (.conj (formula s a b) (formula t a b)))

theorem formula_eval {stage : V} (closed : Internal.Transitive E stage)
    (t : LocalTree) (a b : Fin 3) (env : Fin 3 → V) (ha : E (env a) stage) (hb : E (env b) stage) :
    LocalFormula.eval E (fun x => E x stage) (formula t a b) env ↔
      (relation (E := E) (G := G) stage t).holds (env a) (env b) := by
  induction t generalizing a b env with
  | leaf =>
    exact ⟨fun h => ⟨env b,h,rfl,hb⟩,fun ⟨_,h,eq,_⟩ => by simpa only [eq,formula,LocalFormula.eval,ClassRelation.member] using h⟩
  | node r s t ir is it =>
    let c := spare a b
    have ea (x : V) : LocalFormula.bindValue env c x a = env a :=
      ite_eq_right (Ne.symm (spare_left a b))
    have eb (x : V) : LocalFormula.bindValue env c x b = env b :=
      ite_eq_right (Ne.symm (spare_right a b))
    have ec (x : V) : LocalFormula.bindValue env c x c = x := ite_eq_left rfl
    change (∃ x, E x stage ∧
      LocalFormula.eval E (fun x => E x stage) (formula r a c) (LocalFormula.bindValue env c x) ∧
      LocalFormula.eval E (fun x => E x stage) (formula s b c) (LocalFormula.bindValue env c x)) ∧
      ¬ (LocalFormula.eval E (fun x => E x stage) (formula s a b) env ∧
         LocalFormula.eval E (fun x => E x stage) (formula t a b) env) ↔ _
    refine and_congr ?_ (not_congr (and_congr (is a b env ha hb) (it a b env ha hb)))
    change _ ↔ ∃ x, (relation (E := E) (G := G) stage r).holds (env a) x ∧
      (relation (E := E) (G := G) stage s).holds (env b) x
    have compare (x : V) (hx : E x stage) :=
      and_congr (ir a c (LocalFormula.bindValue env c x) (by rwa [ea]) (by rwa [ec]))
        (is b c (LocalFormula.bindValue env c x) (by rwa [eb]) (by rwa [ec]))
    constructor
    · rintro ⟨x,hx,values⟩
      exact ⟨x,by simpa only [ea,eb,ec] using (compare x hx).mp values⟩
    · rintro ⟨x,left,right⟩
      have hx := (supported closed r left).2
      exact ⟨x,hx,(compare x hx).mpr (by simpa only [ea,eb,ec] using And.intro left right)⟩

theorem preserves (L : ClassAxioms E G) (inhabited : Nonempty V) {w stage j : V} (omega : Internal.Omega E w)
    (mapping : Internal.FunctionInto E j stage stage)
    (elementary : Internal.ElementaryOnRank E w stage j)
    (closed : Internal.Transitive E stage) (t : LocalTree) {a b x y : V}
    (edge : (relation (E := E) (G := G) stage t).holds a b)
    (left : Internal.At E j a x) (right : Internal.At E j b y) :
    (relation (E := E) (G := G) stage t).holds x y := by
  have ⟨aIn,bIn⟩ := supported closed t edge
  let source : Fin 3 → V := fun i => if i = 0 then a else b
  let target : Fin 3 → V := fun i => if i = 0 then x else y
  have good (i : Fin 3) : E (source i) stage := by
    by_cases h : i = 0 <;> simp [source,h,aIn,bIn]
  have moved (i : Fin 3) : Internal.At E j (source i) (target i) := by
    by_cases h : i = 0 <;> simp [source,target,h,left,right]
  have before := (formula_eval (G := G) closed t 0 1 source aIn bIn).mpr edge
  have after := ((L.context inhabited).embedding_preserves_local omega mapping elementary _ source target good moved).mp before
  exact (formula_eval (G := G) closed t 0 1 target
    (mapping.2 a aIn x left) (mapping.2 b bIn y right)).mp after

end LocalTree
end PalomarI3380.Logic.Expanded
