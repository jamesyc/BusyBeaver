import PA215.Source.AXPushDrains
set_option linter.unusedSimpArgs false

namespace PA215.Source.AXPush

/-- The diagonal walk terminates by decreasing X, accumulating its triangular
number. Its inner transfer loops preserve the complete unrelated register frame. -/
theorem pair_loop (s w y : Nat) (f : Registers) :
    ∃ n, Steps exactSites n (configAt 35 ⟨0,w,s,y,f⟩)
      (configAt 41 ⟨0,w,0,y+Cantor.triangle s,f⟩) := by
  induction s generalizing y with
  | zero =>
    refine ⟨1,?_⟩
    apply Steps.cons
    rw [step_35]
    simp only [↓reduceIte,Cantor.triangle,Nat.add_zero]
    exact Steps.refl _
  | succ s ih =>
    obtain ⟨n,hn⟩ := ih (y+1+s)
    have a : Steps exactSites 2 (configAt 35 ⟨0,w,s+1,y,f⟩)
        (configAt 37 ⟨0,w,s,y+1,f⟩) := by
      apply Steps.cons
      rw [step_35]
      simp only [Nat.add_eq_zero_iff,Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
      apply Steps.cons
      rw [step_36]
      exact Steps.refl _
    have b : Steps exactSites (3*s+1) (configAt 37 ⟨0,w,s,y+1,f⟩)
        (configAt 40 ⟨s,w,0,y+1,f⟩) := by
      simpa only [Nat.zero_add] using drain_x 0 w s (y+1) f
    have c : Steps exactSites 1 (configAt 40 ⟨s,w,0,y+1,f⟩)
        (configAt 31 ⟨s,w,0,y+1,f⟩) := by
      apply Steps.cons
      rw [step_40]
      exact Steps.refl _
    have d : Steps exactSites (4*s+1) (configAt 31 ⟨s,w,0,y+1,f⟩)
        (configAt 35 ⟨0,w,s,y+1+s,f⟩) := by
      simpa only [Nat.zero_add] using drain_t_xy s w 0 (y+1) f
    refine ⟨2+(3*s+1)+1+(4*s+1)+n,?_⟩
    simpa only [Cantor.triangle,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((a.append b).append c).append d).append hn

/-- Exact first AX push macro, ordinals25 through43, returning at44.
T is pushed onto W using the actual Cantor encoding; scratch X,Y is restored.
N,L,A,D,H are untouched through the arbitrary frame. -/
theorem push (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (configAt 25 ⟨t,w,0,0,f⟩)
      (configAt 44 ⟨0,Cantor.pair t w,0,0,f⟩) := by
  have a : Steps exactSites (3*t+1) (configAt 25 ⟨t,w,0,0,f⟩)
      (configAt 28 ⟨0,w,t,0,f⟩) := by
    simpa only [Nat.zero_add] using drain_t t w 0 0 f
  have b : Steps exactSites (3*w+1) (configAt 28 ⟨0,w,t,0,f⟩)
      (configAt 31 ⟨w,0,t,0,f⟩) := by
    simpa only [Nat.zero_add] using drain_w 0 w t 0 f
  have c : Steps exactSites (4*w+1) (configAt 31 ⟨w,0,t,0,f⟩)
      (configAt 35 ⟨0,0,t+w,w,f⟩) := by
    simpa only [Nat.zero_add] using drain_t_xy w 0 t 0 f
  obtain ⟨n,hn⟩ := pair_loop (t+w) 0 w f
  have d := drain_y 0 0 0 (w+Cantor.triangle (t+w)) f
  refine ⟨(3*t+1)+(3*w+1)+(4*w+1)+n+(3*(w+Cantor.triangle (t+w))+1),by omega,?_⟩
  simpa only [Cantor.pair,Nat.zero_add,Nat.add_comm] using
    (((a.append b).append c).append hn).append d

#print axioms literal_binding
#print axioms pair_loop
#print axioms push
end PA215.Source.AXPush
