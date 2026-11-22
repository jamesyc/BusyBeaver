module
public import ZF192Support.Calculus.Internal.Codes
public import ZF192Support.Coding.Pairing.UnpairGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable abbrev axHead6 (a d h : M) := (codes (V := M)).head6 d a h
noncomputable abbrev axHead5 (_ d h : M) := (codes (V := M)).head5 d h
noncomputable abbrev axHead4 (a d h : M) := (codes (V := M)).head4 h d a
noncomputable abbrev axHead3 (a d h : M) := (codes (V := M)).head3 h d a
noncomputable abbrev axHead2 (a d h : M) := (codes (V := M)).head2 d a h
noncomputable abbrev axHead1 (_ d h : M) := (codes (V := M)).head1 d h
noncomputable abbrev axRho8 (a d h u : M) := (codes (V := M)).rho8 d a h u
noncomputable abbrev axGate (a d h : M) := (codes (V := M)).bundle h d a

structure Store (M : Type*) where
 t : M
 w : M
 d : M
 h : M
inductive Command (M : Type*) where
 | shift
 | mp (x:M)
 | ax (a x y:M)
noncomputable def gate (a d h:M) : M := if a≠d ∧ a≠h then axGate a d h else 0
noncomputable def implicationHeads (a d h oldd : M) : List M :=
  (codes (V := M)).axImplicationHeads a d h oldd

noncomputable def heads (a d h oldd oldh : M) : List M :=
  implicationHeads a d h oldd ++ [all oldd oldh]
noncomputable def modelCommandEval : Command M → Store M → Option (Store M)
 | .shift,s => if s.t+s.h=1 then none else some ⟨s.h,modelUnpairRight s.w,s.d,modelUnpairLeft s.w⟩
 | .mp x,s => let v:=s.d+x
   if imp s.t v=s.h then some ⟨v,modelCantor 0 s.w,v,0⟩ else some ⟨0,s.w,v,0⟩
 | .ax a x y,s => some ⟨gate a (s.d+x) (s.h+y),
   (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr modelCantor s.w,0,0⟩
/-- Only external FINITE macro lists. Not an internal nonstandard-length evaluator. -/
noncomputable def modelCommandsEval : List (Command M) → Store M → Option (Store M)
 | [],s => some s
 | c::cs,s => (modelCommandEval c s).bind (modelCommandsEval cs)
private lemma cantor_eq_modelCantor (a b : M) : cantor a b = modelCantor a b :=
  (cantor_eq_iff.mpr (modelCantor_equation a b)).symm

lemma modelImp_value (a b : M) : imp a b = 4 * modelCantor a b := by
  simp [imp, cantor_eq_modelCantor]

lemma modelAll_value (i a : M) : all i a = 4 * modelCantor a i + 2 := by
  simp [all, cantor_eq_modelCantor]

lemma four_mul_ne_one (x : M) : 4*x ≠ 1 := by
 intro h
 have hm := congrArg (fun n : M => n % 4) h
 simp at hm

lemma four_mul_ne_four_add_two (x y : M) : 4*x ≠ 4*y+2 := by
 intro h
 have hm := congrArg (fun n : M => n % 4) h
 have h2 : (2 : M) < 4 := Nat.cast_lt.mpr (by decide : (2 : Nat) < 4)
 simp [mod_mul_add', show (0 : M) < 4 by simp, h2] at hm
end ZF192Support.ModelCommands
