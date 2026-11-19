module
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/- Arbitrary-PA-model basis pilot. Induction explicitly requires an arithmetic formula;
this does not promote the existing Nat-only replay or supply its definability witnesses. -/
abbrev NSet (M : Type*) := M → Prop
def an (p q : Prop) := ¬ (p → ¬ q)
def iffP (p q : Prop) := an (p → q) (q → p)
def ex (p : M → Prop) := ¬ ∀ x, ¬ p x
def sb (a : M) (p : M → Prop) := ∀ y, y=a → ∀ x, x=y → p x
def eqs (A B : NSet M) := ∀ x, iffP (A x) (B x)
noncomputable def the (A : NSet M) : M :=
 by
 classical
 exact if h : ∃ a, ∀ x, A x ↔ x=a then Classical.choose h else 0

theorem an_iff (p q : Prop) : an p q ↔ p ∧ q := by
 classical
 constructor
 · intro h
   have hp : p := Classical.byContradiction (fun hn => h (fun h => False.elim (hn h)))
   exact ⟨hp,Classical.byContradiction (fun hn => h (fun _ => hn))⟩
 · rintro ⟨hp,hq⟩ hn; exact hn hp hq
theorem iffP_iff (p q : Prop) : iffP p q ↔ (p ↔ q) := by
 rw [iffP,an_iff]; exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩
theorem ex_iff (p : M → Prop) : ex p ↔ ∃ x,p x := by
 classical
 constructor
 · intro h; apply Classical.byContradiction; intro hn; exact h (fun x hx => hn ⟨x,hx⟩)
 · rintro ⟨x,hx⟩ hn; exact hn x hx
theorem sb_iff (a : M) (p : M → Prop) : sb a p ↔ p a :=
 ⟨fun h => h a rfl a rfl,fun h y hy x hx => by simpa [hx,hy] using h⟩
theorem eqs_iff (A B : NSet M) : eqs A B ↔ ∀ x,A x ↔ B x :=
 ⟨fun h x => (iffP_iff _ _).mp (h x),fun h x => (iffP_iff _ _).mpr (h x)⟩

theorem ax_1 (a b : Prop) : a → b → a := fun ha _ => ha
theorem ax_2 (a b c : Prop) : (a → b → c) → (a → b) → a → c := fun h g x => h x (g x)
theorem ax_3 (a b : Prop) : (¬ a → ¬ b) → b → a := by
 classical
 exact fun h hb => Classical.byContradiction (fun ha => h ha hb)
theorem ax_mp (a b : Prop) : (a → b) → a → b := fun h => h
theorem itru : True := True.intro
/-- Open proof premise means universal validity, not one arbitrary assignment. -/
theorem ax_gen (p : M → Prop) : (∀ x,p x) → ∀ x,p x := fun h => h
theorem ax_4 (p q : M → Prop) : (∀ x,p x → q x) → (∀ x,p x) → ∀ x,q x := fun h g x => h x (g x)
theorem ax_5 (p : Prop) : p → ∀ _x : M,p := fun h _ => h
theorem ax_6 (a : M) : ex (fun x => x=a) := (ex_iff _).mpr ⟨a,rfl⟩
theorem ax_7 (a b c : M) : a=b → a=c → b=c := fun h g => h.symm.trans g
theorem ax_10 (p : M → Prop) : (¬ ∀ x,p x) → ∀ _x : M,¬ ∀ x,p x := fun h _ => h
theorem ax_11 (p : M → M → Prop) : (∀ x y,p x y) → ∀ y x,p x y := fun h y x => h x y
theorem ax_12 (x a : M) (p : M → Prop) : x=a → p x → ∀ y,y=a → p y := by
 intro h hp y hy; have : y=x := hy.trans h.symm; simpa [this] using hp
theorem «elab» (a : M) (p : M → Prop) : iffP (p a) (sb a p) :=
 (iffP_iff _ _).mpr (sb_iff _ _).symm
theorem ax_8 (a b : M) (A : NSet M) : a=b → A a → A b := fun h => h ▸ id
theorem peano1 (a : M) : a+1 ≠ 0 := by
 have h : 0<a+1 := by have := Arithmetic.zero_le a; exact lt_of_lt_of_le Arithmetic.zero_lt_one (by simpa using add_le_add_right this 1)
 exact ne_of_gt h
theorem peano2 (a b : M) : iffP (a+1=b+1) (a=b) :=
 (iffP_iff _ _).mpr ⟨fun h => add_right_cancel h,fun h => by rw [h]⟩

/-- Induction is restricted to an actual arithmetic formula and parameter
assignment. No induction axiom for arbitrary semantic predicates is assumed. -/
theorem peano5_formula (φ : ArithmeticSemiformula Nat 1) (e : Nat → M) :
 sb 0 (fun x => φ.Eval ![x] e) →
 (∀x,φ.Eval ![x] e → sb (x+1) (fun x => φ.Eval ![x] e)) →
 ∀x,φ.Eval ![x] e := by
 letI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
   models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 intro hz hs
 exact InductionScheme.succ_induction (V := M) (C := Set.univ)
   (P := fun x => φ.Eval ![x] e) ⟨e,φ,True.intro,fun _ => Iff.rfl⟩
   ((sb_iff (M := M) 0 (fun x => φ.Eval ![x] e)).mp hz)
   (fun x hx => (sb_iff (M := M) (x+1) (fun x => φ.Eval ![x] e)).mp (hs x hx))
theorem theid (A : NSet M) (a : M) : eqs A (fun x => x=a) → the A=a := by
 intro h
 have hA := (eqs_iff _ _).mp h
 have hex : ∃ a,∀ x,A x ↔ x=a := ⟨a,hA⟩
 simp only [the,dite_eq_left hex]
 have hc := Classical.choose_spec hex
 exact (hA _).mp ((hc _).mpr rfl)
theorem the0 (A : NSet M) : (¬ ex (fun y => eqs A (fun x => x=y))) → the A=0 := by
 intro h
 have hn : ¬ ∃ a,∀ x,A x ↔ x=a := by
   rintro ⟨a,ha⟩
   exact h ((ex_iff _).mpr ⟨a,(eqs_iff _ _).mpr ha⟩)
 simp only [the,dite_eq_right hn]
theorem addeq (a b c d : M) : a=b → c=d → a+c=b+d := by intro h g; subst b; subst d; rfl
theorem muleq (a b c d : M) : a=b → c=d → a*c=b*d := by intro h g; subst b; subst d; rfl
theorem add0 (a : M) : a+0=a := by simp
theorem addS (a b : M) : a+(b+1)=(a+b+1) := by simp [add_assoc]
theorem mul0 (a : M) : a*0=0 := by simp
theorem mulS (a b : M) : a*(b+1)=a*b+a := by simp [mul_add]
end ZF207.MM0ModelPeano
