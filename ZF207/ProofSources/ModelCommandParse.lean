module
public import ModelCodedCommandStep
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def parseCommand (n:M) : Command M × M :=
 let a:=modelUnpairLeft n
 let b:=modelUnpairRight n
 if a=0 then (.shift,b) else if a=1 then (.mp (modelUnpairLeft b),modelUnpairRight b)
 else (.ax (modelPredecessor (modelPredecessor a))
  (modelUnpairLeft (modelUnpairRight b)) (modelUnpairLeft b),
  modelUnpairRight (modelUnpairRight b))
lemma parseCommand_code (c:Command M) (tail:M) : parseCommand (commandCode c tail)=(c,tail) := by
 cases c with
 | shift => simp [commandCode,parseCommand,modelUnpairLeft_pair,modelUnpairRight_pair]
 | mp x => simp [commandCode,parseCommand,modelUnpairLeft_pair,modelUnpairRight_pair]
 | ax a x y =>
   have h0 : a+2≠(0:M) := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:M)<2) (le_add_self))
   have h1 : a+2≠(1:M) := by
    have hh : (1:M)<a+2 := lt_of_lt_of_le (by norm_num : (1:M)<2) (le_add_self)
    exact ne_of_gt hh
   have ha : a+2=(a+1)+1 := by rw [add_assoc]; norm_num
   simp [commandCode,parseCommand,modelUnpairLeft_pair,modelUnpairRight_pair,h0,h1,ha,modelPredecessor_succ]
lemma commandCode_parse (n:M) : commandCode (parseCommand n).1 (parseCommand n).2=n := by
 have hn:=modelUnpair_reconstruct n
 unfold parseCommand
 dsimp only
 split
 · rename_i h0
   simpa only [commandCode,h0] using hn
 · rename_i h0
   split
   · rename_i h1
     simpa only [commandCode,modelUnpair_reconstruct,h1] using hn
   · rename_i h1
     have hp : 0<modelUnpairLeft n := pos_iff_ne_zero.mpr h0
     have he:=modelPredecessor_of_pos (modelUnpairLeft n) hp
     have hp' : 0<modelPredecessor (modelUnpairLeft n) := by
       apply pos_iff_ne_zero.mpr
       intro hz
       rw [hz,zero_add] at he
       exact h1 he.symm
     have he':=modelPredecessor_of_pos (modelPredecessor (modelUnpairLeft n)) hp'
     have hx : modelPredecessor (modelPredecessor (modelUnpairLeft n))+2=modelUnpairLeft n := by
       calc
        _ = (modelPredecessor (modelPredecessor (modelUnpairLeft n))+1)+1 := by rw [add_assoc]; norm_num
        _ = _ := by rw [he',he]
     simpa only [commandCode,hx,modelUnpair_reconstruct] using hn
lemma commandCode_tail_le (c:Command M) (tail:M) : tail≤commandCode c tail := by
 cases c with
 | shift => exact modelCantor_right_le _ _
 | mp x => exact le_trans (modelCantor_right_le _ _) (modelCantor_right_le _ _)
 | ax a x y => exact le_trans (modelCantor_right_le _ _) (le_trans (modelCantor_right_le _ _) (modelCantor_right_le _ _))
lemma parseCommand_next_le (n:M) : (parseCommand n).2≤n := by
 have h:=commandCode_tail_le (parseCommand n).1 (parseCommand n).2
 simpa only [commandCode_parse] using h
lemma command_residual_descends (c:Command M) (tail:M) : tail<commandCode c tail+1 :=
 lt_of_le_of_lt (commandCode_tail_le c tail) (by simp)
end ZF207.ModelCommands
