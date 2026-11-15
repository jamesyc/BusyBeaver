module
public import ModelRuntimeBoxHead
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def modelTok (gap:M) (vs:List M) (spares:M) : Tok → M → M
 | .run b a c,tail => bitRun ((a:M)*gap+(c:M)) (bitValue b) tail
 | .box x,tail => modelBox vs spares x tail
noncomputable def modelTails (gap:M) (vs:List M) (spares:M) (ts:List Tok) (tail:M) : M :=
 ts.foldr (modelTok gap vs spares) tail
lemma modelTails_push (gap:M) (vs:List M) (spares:M) (t:Tok) (ts:List Tok) (tail:M) :
 modelTails gap vs spares (push t ts) tail=modelTok gap vs spares t (modelTails gap vs spares ts tail) := by
 cases t with
 | box x => rfl
 | run b a c =>
  have g:modelTails gap vs spares (match ts with
    | .run b' a' c'::ts' => if b=b' then .run b (a+a') (c+c')::ts' else .run b a c::ts
    | _ => .run b a c::ts) tail = modelTok gap vs spares (.run b a c) (modelTails gap vs spares ts tail) := by
   match ts with
   | [] => rfl
   | .box x::ts => rfl
   | .run b' a' c'::ts' =>
    by_cases hb:b=b'
    · subst b'
      simp only [ite_true,modelTails,List.foldr_cons,modelTok]
      have he:((a+a':Nat):M)*gap+((c+c':Nat):M)=((a:M)*gap+c)+((a':M)*gap+c') := by
       simp only [Nat.cast_add,add_mul]; ac_rfl
      rw [he,bitRun_add]
    · simp only [hb,ite_false,modelTails,List.foldr_cons]
  match a,c with
  | 0,0 => simp [push,modelTok,bitRun_zero]
  | 0,c+1 => exact g
  | a+1,c => exact g
lemma modelTails_norm (gap:M) (vs:List M) (spares:M) (s:List Seg) :
 modelTails gap vs spares (norm s) 0=modelFlat gap vs spares s := by
 induction s with
 | nil => rfl
 | cons x s ih =>
  simp only [norm,List.foldr_cons] at ih ⊢
  rw [modelTails_push,ih,modelFlat_cons]
  cases x with
  | box x => rfl
  | run b a c => rfl
  | bit b =>
   simp only [tokOf,modelTok,modelSeg,Nat.cast_zero,Nat.cast_one,zero_mul,zero_add]
   have he:(1:M)=0+1 := by simp
   rw [he,bitRun_succ,bitRun_zero]
lemma bitRun_blank (n:M) : bitRun n 0 0=0 := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact bitRun_zero _ _
 case succ n ih => rw [bitRun_succ,ih]; simp
lemma modelTails_normL (gap:M) (vs:List M) (spares:M) (s:List Seg) :
 modelTails gap vs spares (normL s) 0=modelFlat gap vs spares s := by
 rw [←modelTails_norm]
 unfold normL
 generalize hR:(norm s).reverse=R
 have hs:norm s=R.reverse := by rw [←hR,List.reverse_reverse]
 rw [hs]
 cases R with
 | nil => rfl
 | cons t ts =>
  cases t with
  | box x => rfl
  | run b a c =>
   cases b with
   | true => rfl
   | false =>
    simp only [List.reverse_cons,modelTails,List.foldr_append,List.foldr_cons,List.foldr_nil,modelTok,bitValue,Bool.false_eq_true,ite_false,bitRun_blank]
lemma model_sMatches_conc {s e:SConf} (gap:M) (vs:List M) (spares:M) (h:sMatches s e=true) :
 modelConc gap vs spares s=modelConc gap vs spares e := by
 obtain ⟨q,onl,l,r⟩:=s
 obtain ⟨q',onl',l',r'⟩:=e
 simp only [sMatches,Bool.and_eq_true,beq_iff_eq] at h
 obtain ⟨⟨⟨rfl,rfl⟩,hr⟩,hl⟩:=h
 have er:modelFlat gap vs spares r=modelFlat gap vs spares r' := by rw [←modelTails_norm,hr,modelTails_norm]
 have el:modelFlat gap vs spares l=modelFlat gap vs spares l' := by rw [←modelTails_normL,hl,modelTails_normL]
 cases onl <;> simp only [modelConc,er,el]
end ZF209.BinaryTape
