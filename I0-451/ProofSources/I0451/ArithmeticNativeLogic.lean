module
public import I0451.ArithmeticNativeRules
public import CKernel.Logic

/-! Interpret the reusable Hilbert rules with the literal syntax and
native proof predicate. The native equality tag supplies substitution
in both arguments of membership. -/
@[expose] public section
namespace I0451.Arithmetization.NativeDerivable

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open ZF207.CKernel.Generic
open I0451.Logic (AxiomEncoding ImplicationBasis)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def nativeCodes : Codes V :=
  ⟨modelImp, modelTag 1, modelTag 3, modelTag 2, 1⟩

noncomputable def hilbert : Logic V where
  toCodes := nativeCodes
  Prov := NativeDerivable
  mp := detach
  gen := generalize
  k := implicationBasis.weakening
  s := implicationBasis.distribution
  peirce := implicationBasis.peirce
  r2 a b c := head (a := a) (b := b) (c := c) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    nativeCodes])
  h1 a b := head (a := a) (b := b) (c := 0) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    nativeCodes, Codes.head1, Codes.ex, Codes.neg, modelNeg])
  h2 a b c := head (a := a) (b := b) (c := c) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    nativeCodes, Codes.head2])

local notation "L" => (hilbert : Logic V)
local infixr:55 " ⟹ " => modelImp

theorem native_eq_witness (x y : V) : (L).Prov ((L).ex x ((L).eq x y)) :=
  head (a := x) (b := y) (c := 0) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    hilbert, nativeCodes, Codes.ex, Codes.neg, modelNeg])

theorem native_eq_join (c a b : V) : (L).Prov ((L).eq c a ⟹ (L).eq c b ⟹ (L).eq a b) :=
  head (a := a) (b := b) (c := c) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    hilbert, nativeCodes])

theorem native_vac_eq {a b c : V} (ha : c ≠ a) (hb : c ≠ b) :
    (L).Prov ((L).eq a b ⟹ (L).all c ((L).eq a b)) := by
  have all : (L).Ctx [] (modelEncoding.bundle a b c) := .thm (bundle ha hb)
  exact all.andRight.andRight.andLeft.andRight.empty

theorem native_vac_mem {a b c : V} (ha : c ≠ a) (hb : c ≠ b) :
    (L).Prov ((L).mem a b ⟹ (L).all c ((L).mem a b)) := by
  have all : (L).Ctx [] (modelEncoding.bundle a b c) := .thm (bundle ha hb)
  exact all.andRight.andRight.andLeft.andLeft.empty

theorem native_eq_refl (x : V) : (L).Prov ((L).eq x x) := by
  have fresh : x + 1 ≠ x := (lt_add_one x).ne'
  have consequence : (L).Prov ((L).eq (x + 1) x ⟹ (L).eq x x) :=
    (L).mp (native_eq_join (x+1) x x) ((implicationBasis (V := V)).contraction _ _)
  exact (Logic.Ctx.existsElim (x + 1) (native_vac_eq fresh fresh)
    (.thm ((L).gen _ consequence)) (.thm (native_eq_witness _ _))).empty

theorem native_eq_symm (a b : V) : (L).Prov ((L).eq a b ⟹ (L).eq b a) := by
  exact (L).mp (native_eq_refl a) ((L).mp (native_eq_join a b a) ((L).exchange _ _ _))

theorem native_eq_trans (a b c : V) : (L).Prov ((L).eq a b ⟹ (L).eq b c ⟹ (L).eq a c) := by
  have symmetry : (L).Ctx [(L).eq a b] ((L).eq b a) := .mp .head (.thm (native_eq_symm a b))
  exact (.mp symmetry (.thm (native_eq_join b a c)) : (L).Ctx [(L).eq a b] _).deduction.empty

theorem native_mem_left (a b w : V) : (L).Prov ((L).eq a b ⟹ (L).mem a w ⟹ (L).mem b w) :=
  head (a := b) (b := w) (c := a) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    hilbert, nativeCodes])

theorem native_mem_right (a b w : V) : (L).Prov ((L).eq a b ⟹ (L).mem w a ⟹ (L).mem w b) :=
  head (a := a) (b := b) (c := w) (x := 0) (by simp [AxiomEncoding.heads, modelEncoding,
    hilbert, nativeCodes])

noncomputable def equality (admissible : V → Prop) : EqLogic V where
  toLogic := hilbert
  E := (L).eq
  ok := admissible
  witness x y _ _ _ :=
    (L).mp (native_eq_witness x y) ((L).existsMono x (native_eq_symm x y))
  eVac a b c ca cb _ _ _ := native_vac_eq ca cb
  memVac a b c ca cb := native_vac_mem ca cb
  eSymm a b _ _ := native_eq_symm a b
  eTrans a b c _ _ _ := native_eq_trans a b c

end I0451.Arithmetization.NativeDerivable
