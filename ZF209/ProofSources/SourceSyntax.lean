module
import Std
@[expose] public section
namespace ZFR
inductive Formula where
 | bot : Formula
 | mem : Nat → Nat → Formula
 | eq : Nat → Nat → Formula
 | and : Formula → Formula → Formula
 | or : Formula → Formula → Formula
 | imp : Formula → Formula → Formula
 | all : Formula → Formula
 | ex : Formula → Formula
 deriving DecidableEq, Repr

def lift (σ : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => σ n + 1
@[simp] theorem lift_zero (σ : Nat → Nat) : lift σ 0 = 0 := rfl
@[simp] theorem lift_succ (σ : Nat → Nat) (n : Nat) : lift σ (n+1) = σ n+1 := rfl

def rename (σ : Nat → Nat) : Formula → Formula
 | .bot => .bot
 | .mem i j => .mem (σ i) (σ j)
 | .eq i j => .eq (σ i) (σ j)
 | .and a b => .and (rename σ a) (rename σ b)
 | .or a b => .or (rename σ a) (rename σ b)
 | .imp a b => .imp (rename σ a) (rename σ b)
 | .all a => .all (rename (lift σ) a)
 | .ex a => .ex (rename (lift σ) a)

theorem lift_comp (σ τ : Nat → Nat) : lift (σ ∘ τ) = lift σ ∘ lift τ := by
 funext n; cases n <;> rfl
@[simp] theorem lift_id : lift id = id := by funext n; cases n <;> rfl

theorem rename_comp (σ τ : Nat → Nat) (a : Formula) :
 rename σ (rename τ a) = rename (σ ∘ τ) a := by
 induction a generalizing σ τ with
 | bot => rfl
 | mem i j => rfl
 | eq i j => rfl
 | and a b ia ib => simp only [rename, ia, ib]
 | or a b ia ib => simp only [rename, ia, ib]
 | imp a b ia ib => simp only [rename, ia, ib]
 | all a ih => simp only [rename, ih, lift_comp]
 | ex a ih => simp only [rename, ih, lift_comp]
@[simp] theorem rename_id (a : Formula) : rename id a = a := by
 induction a with
 | bot => rfl
 | mem i j => rfl
 | eq i j => rfl
 | and a b ia ib => simp only [rename, ia, ib]
 | or a b ia ib => simp only [rename, ia, ib]
 | imp a b ia ib => simp only [rename, ia, ib]
 | all a ih => simp only [rename, lift_id, ih]
 | ex a ih => simp only [rename, lift_id, ih]

def shift (a : Formula) := rename Nat.succ a

def substMap (t : Nat) : Nat → Nat
 | 0 => t
 | n+1 => n

def subst (t : Nat) (a : Formula) := rename (substMap t) a

theorem rename_shift (σ : Nat → Nat) (a : Formula) :
 rename (lift σ) (shift a) = shift (rename σ a) := by
 simp only [shift, rename_comp]
 rfl

theorem rename_subst (σ : Nat → Nat) (t : Nat) (a : Formula) :
 rename σ (subst t a) = subst (σ t) (rename (lift σ) a) := by
 simp only [subst, rename_comp]
 congr 1
 funext n; cases n <;> rfl

end ZFR
