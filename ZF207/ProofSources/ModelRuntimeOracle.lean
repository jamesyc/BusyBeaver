module
public import ModelRuntimeBoxes
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def modelValid (br:Branch) (values:List M) : Prop := values.length=9 ∧
 match br with
 | none => True
 | some (r,z) => if z then values.getD r 0=0 else values.getD r 0≠0
lemma model_list_split (vs:List M) (r:Nat) (h:r<vs.length) :
 ∃pre post,pre.length=r ∧ vs=pre++vs.getD r 0::post := by
 induction vs generalizing r with
 | nil => simp at h
 | cons v vs ih =>
  cases r with
  | zero => exact ⟨[],vs,rfl,rfl⟩
  | succ r =>
   obtain ⟨pre,post,hp,he⟩:=ih r (by simpa using h)
   refine ⟨v::pre,post,by simp [hp],?_⟩
   simpa only [List.cons_append,List.getD_cons_succ] using congrArg (List.cons v) he
lemma model_mark_at (vs:List M) (r q:Nat) (l spares:M)
 (hr:skipTarget q=some r) (hlen:vs.length=9) :
 Reaches (namedState q l (modelBox vs spares (.plain .none) 0))
 (namedLeft (markExit r) l (modelBox vs spares (.mark r) 0)) := by
 obtain ⟨hq,h9⟩:=skipTarget_sk hr
 obtain ⟨pre,post,hp,he⟩:=model_list_split vs r (by omega)
 rw [hq,he,←hp]
 exact model_box_mark pre post _ spares l (by omega)
lemma model_increment_at (vs:List M) (r:Nat) (l spares:M) (h9:r<9) (hlen:vs.length=9) :
 Reaches (namedState 64 l (modelBox vs spares (.mark r) 0))
 (namedLeft 40 l (modelBox vs spares (.plain (.inc r)) 0)) := by
 obtain ⟨pre,post,hp,he⟩:=model_list_split vs r (by omega)
 rw [he,←hp]
 exact model_box_increment pre post _ spares l
lemma model_decrement_zero_at (vs:List M) (r:Nat) (l spares:M) (h9:r<9) (hlen:vs.length=9)
 (hz:vs.getD r 0=0) :
 Reaches (namedState 0 l (modelBox vs (spares+1) (.mark r) 0))
 (namedLeft 97 l (modelBox vs (spares+1) (.plain .none) 0)) := by
 obtain ⟨pre,post,hp,he⟩:=model_list_split vs r (by omega)
 rw [hz] at he
 rw [he,←hp]
 exact model_box_decrement_zero pre post spares l
lemma model_decrement_positive_at (vs:List M) (r:Nat) (l spares:M) (h9:r<9) (hlen:vs.length=9)
 (hz:vs.getD r 0≠0) :
 Reaches (namedState 0 l (modelBox vs spares (.mark r) 0))
 (namedLeft 40 (1+2*l) (modelBox vs spares (.plain (.dec r)) 0)) := by
 obtain ⟨v,hv⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr hz)
 obtain ⟨pre,post,hp,he⟩:=model_list_split vs r (by omega)
 rw [hv] at he
 rw [he,←hp]
 exact model_box_decrement_positive pre post v spares l
theorem model_oracle_sound {q : Nat} {br : Branch} {x x' : BoxSt} {q' : Nat} {extra : Bool}
    {vs : List M} (l spares : M) (ho : oracle q br x = some (q', x', extra)) (hv : modelValid br vs) :
    Reaches (namedState q l (modelBox vs (spares+1) x 0))
      (namedLeft q' (if extra then 1+2*l else l) (modelBox vs (spares+1) x' 0)) := by
  obtain ⟨hlen, hbr⟩ := hv
  cases x with
  | plain e =>
      cases e with
      | none =>
          simp only [oracle, Option.map_eq_some_iff] at ho
          obtain ⟨r, hr, he⟩ := ho
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact model_mark_at vs r q l (spares+1) hr hlen
      | inc r => simp [oracle] at ho
      | dec r => simp [oracle] at ho
  | mark r =>
      simp only [oracle] at ho
      by_cases h9 : r < 9
      · simp only [h9, ite_true] at ho
        by_cases h64 : q = 64
        · subst h64
          simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at ho
          obtain ⟨rfl, rfl, rfl⟩ := ho
          exact model_increment_at vs r l (spares+1) h9 hlen
        · simp only [h64, ite_false] at ho
          by_cases h0 : q = 0
          · subst h0
            simp only [ite_true] at ho
            cases br with
            | none => simp at ho
            | some p =>
                obtain ⟨r', z⟩ := p
                by_cases hrr : r = r'
                · subst hrr
                  simp only [ite_true] at ho
                  cases z with
                  | true =>
                      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at ho
                      obtain ⟨rfl, rfl, rfl⟩ := ho
                      exact model_decrement_zero_at vs r l spares h9 hlen (by simpa using hbr)
                  | false =>
                      simp only [Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at ho
                      obtain ⟨rfl, rfl, rfl⟩ := ho
                      exact model_decrement_positive_at vs r l (spares+1) h9 hlen (by simpa using hbr)
                · simp [hrr] at ho
          · simp [h0] at ho
      · simp [h9] at ho

end ZF207.BinaryTape
