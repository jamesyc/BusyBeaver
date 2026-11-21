module
public import I3_380.Arithmetic.OmegaInduction
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "W" => D.Points

theorem zero_plus (b : W) : 0 + b = b := by
  refine D.induction_via (P := fun i => 0 + i = i) (“i. 0 + i = i” : ArithmeticSemisentence 1) Empty.elim
    (fun i => by simp) (D.plus_zero 0) (fun i ih => ?_) b
  rw [D.plus_succ,ih]

theorem succ_plus (a b : W) : D.successor a + b = D.successor (a + b) := by
  refine D.induction_via (P := fun i => D.successor a + i = D.successor (a+i)) (“i. (&(0 : Fin 1) + 1) + i = (&(0 : Fin 1) + i) + 1” :
    ArithmeticSemiformula (Fin 1) 1) ![a]
    (fun i => by simp [D.plus_one])
    (by rw [D.plus_zero,D.plus_zero]) (fun i ih => ?_) b
  rw [D.plus_succ,ih,D.plus_succ]

theorem plus_comm (a b : W) : a + b = b + a := by
  refine D.induction_via (P := fun i => a+i = i+a) (“i. &(0 : Fin 1) + i = i + &(0 : Fin 1)” :
    ArithmeticSemiformula (Fin 1) 1) ![a] (fun i => by simp)
    (by rw [D.plus_zero,D.zero_plus]) (fun i ih => ?_) b
  rw [D.plus_succ,D.succ_plus,ih]

theorem plus_assoc (a b c : W) : (a + b) + c = a + (b + c) := by
  refine D.induction_via (P := fun i => (a+b)+i = a+(b+i)) (“i. (&(0 : Fin 2) + &(1 : Fin 2)) + i = &(0 : Fin 2) + (&(1 : Fin 2) + i)” :
    ArithmeticSemiformula (Fin 2) 1) ![a,b] (fun i => by simp)
    (by rw [D.plus_zero,D.plus_zero]) (fun i ih => ?_) c
  rw [D.plus_succ,ih,D.plus_succ,D.plus_succ]

theorem plus_swap (a b c : W) : (a+b)+c = (a+c)+b := by
  rw [D.plus_assoc,D.plus_comm b c,← D.plus_assoc]

theorem plus_lt_plus {a b : W} (ab : a < b) (c : W) : a+c < b+c := by
  refine D.induction_via (P := fun i => a+i < b+i) (“i. &(0 : Fin 2) + i < &(1 : Fin 2) + i” :
    ArithmeticSemiformula (Fin 2) 1) ![a,b] (fun i => by simp)
    (by simpa only [D.plus_zero] using ab) (fun i ih => ?_) c
  rw [D.plus_succ,D.plus_succ]
  exact D.succ_mono ih

theorem plus_lt_plus_left {a b : W} (ab : a < b) (c : W) : c+a < c+b := by
  rw [D.plus_comm c a,D.plus_comm c b]
  exact D.plus_lt_plus ab c

theorem one_le_of_positive {a : W} (h : 0 < a) : (1 : W) < a ∨ (1 : W) = a := by
  rcases D.nat_predecessor a with rfl | ⟨b,rfl⟩
  · exact (D.lt_irrefl 0 h).elim
  rcases D.zero_le b with greater | eq
  · exact Or.inl (D.succ_mono greater)
  · exact Or.inr (congrArg D.successor eq)

theorem difference (a b : W) (h : a < b) : ∃ c : W, (c < b ∨ c = b) ∧ a+c=b := by
  have all : ∀ b : W, a < b → ∃ c : W, (c < b ∨ c = b) ∧ a+c=b := by
    refine D.induction_via (P := fun i => a < i → ∃ c : W, (c < i ∨ c = i) ∧ a+c=i) (“i. &(0 : Fin 1) < i → ∃ c, (c < i ∨ c = i) ∧ &(0 : Fin 1) + c = i” :
      ArithmeticSemiformula (Fin 1) 1) ![a] (fun i => by simp)
      (fun no => ?_) (fun i ih bound => ?_)
    · exact (((L.context inhabited).empty_mem _ no)).elim
    · rcases (D.lt_successor a i).mp bound with below | rfl
      · obtain ⟨c,size,eq⟩ := ih below
        use D.successor c
        exact ⟨size.imp (fun h => D.succ_mono h) (congrArg D.successor),by rw [D.plus_succ,eq]⟩
      · have positive : (0 : W) < D.successor a := (D.lt_successor _ _).mpr (D.zero_le a)
        exact ⟨1,D.one_le_of_positive positive,D.plus_one a⟩
  exact all b h

end PalomarI3380.Logic.Expanded.OmegaDomain
