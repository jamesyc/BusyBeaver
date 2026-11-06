import PA215.Source.AXPushSteps
import PA215.Source.Cantor

namespace PA215.Source.AXPush

theorem drain_t (t w x y : Nat) (f : Registers) :
    Steps exactSites (3*t+1) (configAt 25 ⟨t,w,x,y,f⟩)
      (configAt 28 ⟨0,w,x+t,y,f⟩) := by
  induction t generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_25]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have he : 3*(t+1)+1 = (3*t+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_25]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_26]
    apply Steps.cons
    rw [step_27]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem drain_w (t w x y : Nat) (f : Registers) :
    Steps exactSites (3*w+1) (configAt 28 ⟨t,w,x,y,f⟩)
      (configAt 31 ⟨t+w,0,x,y,f⟩) := by
  induction w generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_28]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ w ih =>
    have he : 3*(w+1)+1 = (3*w+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_28]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_29]
    apply Steps.cons
    rw [step_30]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem drain_t_xy (t w x y : Nat) (f : Registers) :
    Steps exactSites (4*t+1) (configAt 31 ⟨t,w,x,y,f⟩)
      (configAt 35 ⟨0,w,x+t,y+t,f⟩) := by
  induction t generalizing x y with
  | zero =>
    apply Steps.cons
    rw [step_31]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have he : 4*(t+1)+1 = (4*t+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_31]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_32]
    apply Steps.cons
    rw [step_33]
    apply Steps.cons
    rw [step_34]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1) (y+1)

theorem drain_x (t w x y : Nat) (f : Registers) :
    Steps exactSites (3*x+1) (configAt 37 ⟨t,w,x,y,f⟩)
      (configAt 40 ⟨t+x,w,0,y,f⟩) := by
  induction x generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_37]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_37]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_38]
    apply Steps.cons
    rw [step_39]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem drain_y (t w x y : Nat) (f : Registers) :
    Steps exactSites (3*y+1) (configAt 41 ⟨t,w,x,y,f⟩)
      (configAt 44 ⟨t,w+y,x,0,f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_41]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ y ih =>
    have he : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_41]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_42]
    apply Steps.cons
    rw [step_43]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (w+1)

end PA215.Source.AXPush
