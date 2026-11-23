module
public import I3_334Support.Arithmetic.Numerals
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pushBit (bit : Bool) (tail : M) : M :=
  2 * tail + (bit.toNat : M)

@[simp] theorem pushBit_div (b : Bool) (tail : M) : divIn (pushBit b tail) 2 = tail := by
  apply div_mul_add'
  cases b <;> simp

@[simp] theorem pushBit_rem (b : Bool) (tail : M) : remIn (pushBit b tail) 2 = (b.toNat : M) := by
  unfold remIn pushBit
  rw [mod_mul_add' _ _ (by simp)]
  apply mod_eq_self_of_lt
  cases b <;> simp

@[simp] theorem pushBit_false_zero : pushBit false (0 : M) = 0 := by simp [pushBit]

theorem pushBit_split (x : M) : ∃ b, pushBit b (divIn x 2) = x := by
  have total := Arithmetic.div_add_mod x 2
  rcases mod_two x with zero | one
  · exact ⟨false,by simpa [pushBit,divIn,zero] using total⟩
  · exact ⟨true,by simpa [pushBit,divIn,one] using total⟩

noncomputable def packWord (word : List Bool) (tail : M) : M :=
  word.foldr pushBit tail

@[simp] theorem packWord_nil (tail : M) : packWord [] tail = tail := rfl

@[simp] theorem packWord_cons (b : Bool) (word : List Bool) (tail : M) :
    packWord (b :: word) tail = pushBit b (packWord word tail) := rfl

theorem packWord_append (initial suffix : List Bool) (tail : M) :
    packWord (initial ++ suffix) tail = packWord initial (packWord suffix tail) :=
  List.foldr_append

noncomputable def fromLeft (q : Nat) (left right : M) : M :=
  encode (q : M) (divIn left 2) (2*right+remIn left 2)

theorem fromLeft_pushBit (q : Nat) (b : Bool) (l r : M) :
    fromLeft q (pushBit b l) r = encode (q : M) l (pushBit b r) := by
  rw [fromLeft,pushBit_div,pushBit_rem]
  rfl

def Reaches (m : Machine) (source target : M) : Prop :=
  ∃ steps : M, clock m.workingStates m.packedRows steps source = target

namespace Reaches

theorem definable (m : Machine) : 𝚺ᴬ₁-Relation (Reaches (M := M) m) := by
  unfold Reaches
  definability

theorem refl (m : Machine) (source : M) : Reaches m source source :=
  ⟨0,clock_zero _ _ _⟩

theorem trans {m : Machine} {a b c : M} (first : Reaches m a b) (next : Reaches m b c) :
    Reaches m a c := by
  obtain ⟨i,hi⟩ := first
  obtain ⟨j,hj⟩ := next
  exact ⟨i+j,by rw [clock_add,hi,hj]⟩

theorem single {m : Machine} {a b : M} (edge : tick m.workingStates m.packedRows a = b) :
    Reaches m a b := by
  exact ⟨1,(clock_one _ _ _).trans edge⟩

private theorem row_fields (q : Nat) (w d : Bool) :
    Nat.div (4*q+2*w.toNat+d.toNat) 4 = q ∧
    Nat.mod (Nat.div (4*q+2*w.toNat+d.toNat) 2) 2 = w.toNat ∧
    Nat.mod (4*q+2*w.toNat+d.toNat) 2 = d.toNat := by
  have hw : w.toNat < 2 := by cases w <;> decide
  have hd : d.toNat < 2 := by cases d <;> decide
  change (4*q+2*w.toNat+d.toNat) / 4 = q ∧
    (4*q+2*w.toNat+d.toNat) / 2 % 2 = w.toNat ∧
    (4*q+2*w.toNat+d.toNat) % 2 = d.toNat
  omega

theorem tick_of_row {m : Machine} {q target : Nat} {read write dir : Bool}
    (active : q < m.workingStates) (row : m.row q read.toNat = 4*target+2*write.toNat+dir.toNat)
    (l r : M) :
    tick m.workingStates m.packedRows (encode (q : M) l (pushBit read r)) =
      if dir then encode (target : M) (pushBit write l) r
      else fromLeft target l (pushBit write r) := by
  classical
  let data := 4*target+2*write.toNat+dir.toNat
  have working : (q : M) < (m.workingStates : M) := by exact_mod_cast active
  have digitEq : digit m.packedRows (q : M) (pushBit read r) = (data : M) := by
    rw [digit_at_row m,pushBit_rem]
    cases read
    · simpa [data] using congrArg (fun n : Nat => (n : M)) row
    · simpa [data] using congrArg (fun n : Nat => (n : M)) row
  have next : Nat.div data 4 = target := (row_fields target write dir).1
  have written : Nat.mod (Nat.div data 2) 2 = write.toNat := (row_fields target write dir).2.1
  have direction : Nat.mod data 2 = dir.toNat := (row_fields target write dir).2.2
  have q' : divIn (data : M) 4 = (target : M) := by
    simpa only [Nat.cast_ofNat,next] using divIn_cast (M := M) data 4
  have w' : remIn (divIn (data : M) 2) 2 = (write.toNat : M) := by
    have half := divIn_cast (M := M) data 2
    have rem := remIn_cast (M := M) (Nat.div data 2) 2
    simpa only [Nat.cast_ofNat,written] using (congrArg (fun x => remIn x ((2 : Nat) : M)) half).trans rem
  have d' : remIn (data : M) 2 = (dir.toNat : M) := by
    simpa only [Nat.cast_ofNat,direction] using remIn_cast (M := M) data 2
  simp only [tick,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,working,↓reduceIte,digitEq,q',w',d',pushBit_div]
  cases dir
  · have two : (2 : M) * 2 = 4 := by exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
    simp [fromLeft,encode,pushBit,mul_add,← mul_assoc,two]
  · simp [pushBit]

theorem step_right {m : Machine} {q target : Nat} {read write : Bool}
    (active : q < m.workingStates) (row : m.row q read.toNat = 4*target+2*write.toNat+1)
    (l r : M) :
    Reaches m (encode (q : M) l (pushBit read r)) (encode (target : M) (pushBit write l) r) :=
  .single (tick_of_row (dir := true) active row l r)

theorem step_left {m : Machine} {q target : Nat} {read write : Bool}
    (active : q < m.workingStates) (row : m.row q read.toNat = 4*target+2*write.toNat)
    (l r : M) :
    Reaches m (encode (q : M) l (pushBit read r)) (fromLeft target l (pushBit write r)) := by
  apply single
  apply tick_of_row (dir := false) active
  simpa only [Bool.toNat_false,Nat.add_zero] using row

end Reaches
end PalomarI3380.ArithmeticMachine
