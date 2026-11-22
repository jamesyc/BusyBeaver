module
public import ZF192Support.Calculus.Codes.Evaluation
@[expose] public section
namespace CCodeSoundness
universe u
variable {α : Type u}
def impCode (a b : Nat) : Nat := 4*cantor a b
def memCode (a b : Nat) : Nat := 4*cantor a b+1
def allCode (x a : Nat) : Nat := 4*cantor a x+2
def eqCode (a b : Nat) : Nat := 4*cantor a b+3

theorem evalCode_imp (mem : α → α → Prop) (a b : Nat) (s : Assignment α) :
    evalCode mem (impCode a b) s ↔ (evalCode mem a s → evalCode mem b s) := by
  have h := evalCode_of_formula (.imp (decode a) (decode b)) mem s
  simpa only [Formula.code, Formula.eval, decode_code, impCode, evalCode] using h

theorem evalCode_mem (mem : α → α → Prop) (a b : Nat) (s : Assignment α) :
    evalCode mem (memCode a b) s ↔ mem (s a) (s b) := by
  exact evalCode_of_formula (.mem a b) mem s

theorem evalCode_all (mem : α → α → Prop) (x a : Nat) (s : Assignment α) :
    evalCode mem (allCode x a) s ↔ ∀ v, evalCode mem a (update s x v) := by
  have h := evalCode_of_formula (.all x (decode a)) mem s
  simpa only [Formula.code, Formula.eval, decode_code, allCode, evalCode] using h

theorem evalCode_eq (mem : α → α → Prop) (a b : Nat) (s : Assignment α) :
    evalCode mem (eqCode a b) s ↔ s a = s b :=
  evalCode_of_formula (.eq a b) mem s

theorem evalCode_one_false (mem : α → α → Prop) (irreflexive : ∀ x, ¬ mem x x)
    (s : Assignment α) : evalCode mem 1 s ↔ False := by
  have h : memCode 0 0 = 1 := rfl
  rw [← h, evalCode_mem]
  exact ⟨fun hm => irreflexive (s 0) hm, False.elim⟩

def head1Code (a d h : Nat) := impCode (allCode d a) (impCode (allCode d (impCode a h)) (allCode d h))
def head2Code (_a d h : Nat) := impCode (allCode d (impCode (eqCode h d) 1)) 1
def head3Code (a d h : Nat) := impCode (eqCode h d) (impCode (memCode a h) (memCode a d))
def head4Code (a d h : Nat) := impCode (memCode h d) (impCode (eqCode h a) (memCode a d))
def head5Code (a d h : Nat) := impCode (allCode d (allCode a h)) (allCode a (allCode d h))
def head6Code (_a d h : Nat) := impCode (impCode (allCode d (impCode (allCode d h) 1)) 1) h
def rho8Code (a d h v : Nat) := impCode (impCode (impCode h v) d) (impCode (impCode d h) (impCode a h))

theorem eval_head1 (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head1Code a d h) s := by
  simp only [head1Code, evalCode_imp, evalCode_all]
  exact head1_sound d (evalCode mem a) (evalCode mem h) s

theorem eval_head2 (mem : α → α → Prop) (irr : ∀ x, ¬ mem x x) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head2Code a d h) s := by
  simp only [head2Code, evalCode_imp, evalCode_all, evalCode_eq, evalCode_one_false mem irr]
  exact head2_sound d h s

theorem eval_head3 (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head3Code a d h) s := by
  simp only [head3Code, evalCode_imp, evalCode_mem, evalCode_eq]
  exact head3_sound mem a d h s

theorem eval_head4 (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head4Code a d h) s := by
  simp only [head4Code, evalCode_imp, evalCode_mem, evalCode_eq]
  exact head4_sound mem a d h s

theorem eval_head5 (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head5Code a d h) s := by
  simp only [head5Code, evalCode_imp, evalCode_all]
  exact head5_sound a d (evalCode mem h) s

theorem eval_head6 (mem : α → α → Prop) (irr : ∀ x, ¬ mem x x) (a d h : Nat) (s : Assignment α) :
    evalCode mem (head6Code a d h) s := by
  simp only [head6Code, evalCode_imp, evalCode_all, evalCode_one_false mem irr]
  exact head6_sound d (evalCode mem h) s

theorem eval_rho8 (mem : α → α → Prop) (a d h v : Nat) (s : Assignment α) :
    evalCode mem (rho8Code a d h v) s := by
  simp only [rho8Code, evalCode_imp]
  exact rho8_sound _ _ _ _

end CCodeSoundness
