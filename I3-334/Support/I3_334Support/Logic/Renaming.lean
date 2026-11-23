module
public import I3_334Support.Logic.I3
@[expose] public section

namespace PalomarI3380.Logic

theorem lift_comp (f g : Nat → Nat) : lift (f ∘ g) = lift f ∘ lift g := by
  funext i
  cases i <;> rfl

theorem rename_comp (p : Formula) (f g : Nat → Nat) :
    rename f (rename g p) = rename (f ∘ g) p := by
  induction p generalizing f g <;> simp [rename,Function.comp_apply, * ,lift_comp]

theorem rename_identity (p : Formula) : rename id p = p := by
  have lift_id : lift id = id := by
    funext i
    cases i <;> rfl
  induction p <;> simp [rename, *]

theorem rename_agree (p : Formula) {n : Nat} (bound : Bound p n) (f g : Nat → Nat)
    (agrees : ∀ i, i < n → f i = g i) : rename f p = rename g p := by
  induction p generalizing n f g with
  | bot => rfl
  | eq i j | mem i j => simp only [rename,agrees i bound.1,agrees j bound.2]
  | and p q ip iq | or p q ip iq | imp p q ip iq =>
    simp only [rename,ip bound.1 f g agrees,iq bound.2 f g agrees]
  | all p ih | ex p ih =>
    have under (i : Nat) (hi : i < n+1) : lift f i = lift g i := by
      cases i with
      | zero => rfl
      | succ i => simp only [lift,agrees i (by omega)]
    simp only [rename,ih bound (lift f) (lift g) under]

theorem rename_closed (p : Formula) (closed : Closed p) (f : Nat → Nat) : rename f p = p :=
  (rename_agree p closed f id (fun _ h => by omega)).trans (rename_identity p)

theorem rename_bounded (p : Formula) {n m : Nat} (h : Bound p n) (σ : Nat → Nat)
    (range : ∀ i, i < n → σ i < m) : Bound (rename σ p) m := by
  induction p generalizing n m σ with
  | bot => trivial
  | eq i j | mem i j => exact ⟨range i h.1,range j h.2⟩
  | and p q ip iq | or p q ip iq | imp p q ip iq => exact ⟨ip h.1 σ range,iq h.2 σ range⟩
  | all p ih | ex p ih =>
    apply ih h (lift σ)
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact Nat.succ_lt_succ (range i (by omega))

theorem bound_weaken {p : Formula} {n m : Nat} (inSmall : Bound p n) (h : n ≤ m) : Bound p m := by
  simpa only [rename_identity] using (rename_bounded p inSmall id (fun _ hi => Nat.lt_of_lt_of_le hi h))

theorem formula_bounded (p : Formula) : ∃ n, Bound p n := by
  induction p with
  | bot => exact ⟨0,trivial⟩
  | mem a b | eq a b => exact ⟨max a b + 1,by omega,by omega⟩
  | and p q ip iq | or p q ip iq | imp p q ip iq =>
    obtain ⟨m,hm⟩ := ip
    obtain ⟨n,hn⟩ := iq
    exact ⟨max m n,bound_weaken hm (by omega),bound_weaken hn (by omega)⟩
  | all p ih | ex p ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n,bound_weaken (p := p) (m := n+1) hn (by omega)⟩

theorem rename_shift (p : Formula) (σ : Nat → Nat) :
    rename (lift σ) (shift p) = shift (rename σ p) := by
  unfold shift
  rw [rename_comp,rename_comp]
  congr 1

theorem rename_shift_comp (σ : Nat → Nat) : rename (lift σ) ∘ shift = shift ∘ rename σ :=
  funext fun p => rename_shift p σ

theorem rename_subst (p : Formula) (σ : Nat → Nat) (t : Nat) :
    rename σ (subst t p) = subst (σ t) (rename (lift σ) p) := by
  unfold subst
  rw [rename_comp,rename_comp]
  congr 1
  funext i
  cases i <;> rfl

def Row.rename (σ : Nat → Nat) : Row → Row
  | .seq Γ p => .seq (Γ.map (Logic.rename σ)) (Logic.rename σ p)
  | .branches Γ a b c =>
    .branches (Γ.map (Logic.rename σ)) (Logic.rename σ a) (Logic.rename σ b) (Logic.rename σ c)

theorem ND.rename {row : Row} (h : ND row) (σ : Nat → Nat) : ND (row.rename σ) := by
  induction h generalizing σ with
  | ctx h => exact .ctx (List.mem_map.mpr ⟨_,h,rfl⟩)
  | pc Γ a b => exact .pc _ _ _
  | ii h ih => exact .ii (ih σ)
  | ie h k ih ik => exact .ie (ih σ) (ik σ)
  | «exp» h ih => exact .exp (ih σ)
  | ci h k ih ik => exact .ci (ih σ) (ik σ)
  | ce1 h ih => exact .ce1 (ih σ)
  | ce2 h ih => exact .ce2 (ih σ)
  | di1 h ih => exact .di1 (ih σ)
  | di2 h ih => exact .di2 (ih σ)
  | branchPair h k ih ik => exact .branchPair (ih σ) (ik σ)
  | de h k ih ik => exact .de (ih σ) (ik σ)
  | wk subset h ih =>
    apply ND.wk _ (ih σ)
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨q,subset q hq,rfl⟩
  | allI h ih =>
    apply ND.allI
    simpa only [Row.rename,shiftContext,List.map_map,rename_shift_comp] using ih (lift σ)
  | allE t h ih =>
    simpa only [Row.rename,rename_subst] using ND.allE (σ t) (ih σ)
  | exI t h ih =>
    apply ND.exI (σ t)
    simpa only [Row.rename,rename_subst] using ih σ
  | exE h k ih ik =>
    apply ND.exE (ih σ)
    simpa only [Row.rename,shiftContext,List.map_cons,List.map_map,rename_shift_comp,rename_shift]
      using ik (lift σ)

theorem allPrefix_bound {p : Formula} {m : Nat} (n : Nat) (h : Bound p (m+n)) :
    Bound (allPrefix n p) m := by
  induction n generalizing m with
  | zero => exact h
  | succ n ih => exact ih (m := m+1) (by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using h)

theorem fixed_closed {p : Formula} (h : FixedAxiom p) : Closed p := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (checkBound_sound _ _).mp rfl

theorem separation_closed {n : Nat} {p : Formula} (h : Bound p (n+1)) :
    Closed (separationSchema n p) := by
  apply allPrefix_bound
  have shifted := rename_bounded p h sepIndex (m := n+3) (fun i hi => by unfold sepIndex; split <;> omega)
  simpa (disch := omega) [separationFormula,sourceIff,Bound,Nat.add_assoc] using shifted

theorem replacement_closed {n : Nat} {p : Formula} (h : Bound p (n+2)) :
    Closed (replacementSchema n p) := by
  apply allPrefix_bound
  have first := rename_bounded p h repAIndex (m := n+3) (fun i hi => by unfold repAIndex; split <;> (try split) <;> omega)
  have second := rename_bounded p h repBIndex (m := n+3) (fun i hi => by unfold repBIndex; split <;> (try split) <;> omega)
  have third := rename_bounded p h repCIndex (m := n+4) (fun i hi => by unfold repCIndex; split <;> (try split) <;> omega)
  simp (disch := omega) only [replacementFormula,functionalityFormula,sourceIff,Bound,Nat.zero_add,
    Nat.add_assoc,Nat.reduceAdd,first,second,third,true_and,and_true]
  omega

theorem zfci3_closed {p : Formula} (h : ZFCI3Axiom p) : Closed p := by
  rcases h with (fixed | ⟨_,_,bound,rfl⟩ | ⟨_,_,bound,rfl⟩) | rfl | rfl
  · exact fixed_closed fixed
  · exact separation_closed bound
  · exact replacement_closed bound
  · exact choice_closed
  · exact i3_closed

end PalomarI3380.Logic
