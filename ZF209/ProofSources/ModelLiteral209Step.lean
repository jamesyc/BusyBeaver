module
public import ModelBinaryTape
public import M209.Literal
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation M6.Reference230
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def boolNat (b:Bool) : Nat := if b then 1 else 0
lemma boolNat_cast (b:Bool) : (boolNat b:M)=bitValue b := by cases b <;> simp [boolNat,bitValue]
def moveFormula (read write dir:Bool) (target:Nat) : ArithmeticSemisentence 6 :=
 let rb:=boolNat read
 let wb:=boolNat write
 if dir then
 “q l r q' l' r'. ∃rt, r=↑rb+2*rt ∧ q'=↑target ∧ l'=↑wb+2*l ∧ r'=rt”
 else
 “q l r q' l' r'. ∃rt, r=↑rb+2*rt ∧ q'=↑target ∧
 ∃lt, ∃b, (b=0 ∨ b=1) ∧ l=b+2*lt ∧ l'=lt ∧ r'=b+2*↑wb+4*rt”
lemma moveFormula_eval (read write dir:Bool) (target:Nat) (v:Fin 6→M) :
 (moveFormula read write dir target).Evalb v ↔
 move read write dir (target:M) ⟨v 0,v 1,v 2⟩ ⟨v 3,v 4,v 5⟩ := by
 have hadd (a b:M) : Semiterm.Operator.val ![a,b] (op(+) : Semiterm.Operator ℒₒᵣ 2)=a+b := rfl
 have hmul (a b:M) : Semiterm.Operator.val ![a,b] (op(*) : Semiterm.Operator ℒₒᵣ 2)=a*b := rfl
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 cases dir <;> simp [moveFormula,move,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,numeral_eq_natCast,boolNat_cast,hv,hadd,hmul]
 all_goals simp [exists_or,and_left_comm,and_assoc]
def siteFormula (q:Nat) (read:Bool) (row:Row) : ArithmeticSemisentence 6 :=
 match row with
 | none => ⊥
 | some (write,dir,target) => (“#0=↑q”:ArithmeticSemisentence 6) ⋏ moveFormula read write dir target
def tableFormula (tm:M6.Zip.TMN) (sites:List Nat) : ArithmeticSemisentence 6 :=
 sites.foldr (fun q rest=>siteFormula q false (tm q false) ⋎ siteFormula q true (tm q true) ⋎ rest) ⊥
def literalStepFormula : ArithmeticSemisentence 6 := tableFormula M209.literal (List.range 209)
def literalStep (s t:State M) : Prop := ∃q:Nat,q<209 ∧ s.q=(q:M) ∧
 ∃read write dir target,M209.literal q read=some (write,dir,target) ∧ move read write dir (target:M) s t
lemma siteFormula_eval (q:Nat) (read:Bool) (row:Row) (v:Fin 6→M) :
 (siteFormula q read row).Evalb v ↔ v 0=(q:M) ∧
 ∃write dir target,row=some (write,dir,target) ∧
 move read write dir (target:M) ⟨v 0,v 1,v 2⟩ ⟨v 3,v 4,v 5⟩ := by
 cases row with
 | none => simp [siteFormula]
 | some row => rcases row with ⟨write,dir,target⟩; cases write <;> cases dir <;> simp [siteFormula,moveFormula_eval,numeral_eq_natCast]
lemma tableFormula_eval (tm:M6.Zip.TMN) (sites:List Nat) (v:Fin 6→M) :
 (tableFormula tm sites).Evalb v ↔ ∃q∈sites,v 0=(q:M) ∧
 ∃read write dir target,tm q read=some (write,dir,target) ∧
 move read write dir (target:M) ⟨v 0,v 1,v 2⟩ ⟨v 3,v 4,v 5⟩ := by
 induction sites with
 | nil => simp [tableFormula]
 | cons q sites ih =>
   change ((siteFormula q false (tm q false)).Evalb v ∨
    (siteFormula q true (tm q true)).Evalb v ∨ (tableFormula tm sites).Evalb v) ↔ _
   rw [siteFormula_eval,siteFormula_eval,ih]
   simp only [List.mem_cons,exists_eq_or_imp]
   constructor
   · rintro (⟨hq,w,d,n,hr,hm⟩|⟨hq,w,d,n,hr,hm⟩|hs)
     · exact Or.inl ⟨hq,false,w,d,n,hr,hm⟩
     · exact Or.inl ⟨hq,true,w,d,n,hr,hm⟩
     · exact Or.inr hs
   · rintro (⟨hq,b,w,d,n,hr,hm⟩|hs)
     · cases b with
       | false => exact Or.inl ⟨hq,w,d,n,hr,hm⟩
       | true => exact Or.inr (Or.inl ⟨hq,w,d,n,hr,hm⟩)
     · exact Or.inr (Or.inr hs)
lemma literalStepFormula_eval (v:Fin 6→M) :
 literalStepFormula.Evalb v ↔ literalStep ⟨v 0,v 1,v 2⟩ ⟨v 3,v 4,v 5⟩ := by
 rw [literalStepFormula,tableFormula_eval]
 simp only [List.mem_range,literalStep]
end ZF209.BinaryTape
