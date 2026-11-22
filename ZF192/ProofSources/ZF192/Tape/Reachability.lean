module
public import ZF192.Tape.History
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact physical macro contract retaining an arbitrary earlier rooted history. -/
def Reaches (s t:State M) : Prop := ∀initial hist:M,
 runHistory initial hist → modelListHead hist=stateCode s →
 ∃out,runHistory initial out ∧ modelListHead out=stateCode t
lemma Reaches.refl (s:State M) : Reaches s s := by
 intro initial hist hh he; exact ⟨hist,hh,he⟩
lemma Reaches.step {s t:State M} (h:literalStep s t) : Reaches s t := by
 intro initial hist hh he
 refine ⟨modelListCons (stateCode t) hist,?_,modelListHead_cons _ _⟩
 apply runHistory_extend hh
 rw [he]; exact ⟨s,t,rfl,rfl,h⟩
lemma Reaches.trans {s t u:State M} (h:Reaches s t) (g:Reaches t u) : Reaches s u := by
 intro initial hist hh he
 obtain ⟨middle,hm,hem⟩:=h initial hist hh he
 exact g initial middle hm hem
lemma Reaches.of_eq {s t:State M} (h:s=t) : Reaches s t := h ▸ Reaches.refl s
/-- A physical first step followed by a model-internal run. -/
def Reaches1 (s t : State M) : Prop :=
  ∃ u, literalStep s u ∧ Reaches u t

lemma Reaches1.reaches {s t : State M} (h : Reaches1 s t) : Reaches s t := by
  obtain ⟨u, first, rest⟩ := h
  exact (Reaches.step first).trans rest

lemma Reaches1.trans {s t u : State M} (first : Reaches1 s t) (rest : Reaches t u) :
    Reaches1 s u := by
  obtain ⟨next, hstep, htail⟩ := first
  exact ⟨next, hstep, htail.trans rest⟩

lemma physical_right (q target : Nat) (read write : Bool) (l r : M)
    (row : M192.literal q read = some (write,true,target)) :
    literalStep ⟨(q:M),l,bitValue read+2*r⟩ ⟨(target:M),bitValue write+2*l,r⟩ :=
  ⟨q,literal_row_bound _ _ _ _ _ row,rfl,read,write,true,target,row,r,rfl,rfl,rfl,rfl⟩

lemma physical_left (q target : Nat) (read write leftbit : Bool) (l r : M)
    (row : M192.literal q read = some (write,false,target)) :
    literalStep ⟨(q:M),bitValue leftbit+2*l,bitValue read+2*r⟩
      ⟨(target:M),l,bitValue leftbit+2*bitValue write+4*r⟩ :=
  ⟨q,literal_row_bound _ _ _ _ _ row,rfl,read,write,false,target,row,
   r,rfl,rfl,l,bitValue leftbit,bitValue_cases _,rfl,rfl,rfl⟩

end ZF192.BinaryTape
