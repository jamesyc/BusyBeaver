module
public import DirectWitnessParser
public import DirectContextUncons
@[expose] public section
namespace RosserDirect.WitnessContextCheck
open Turing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384

inductive Q where
 | uncons (q : ContextUncons.Control) | begin | axiom (q : WitnessParser.Q)
 | finish | accept | reject
 deriving DecidableEq, Fintype, Inhabited
abbrev C := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
abbrev S := TM2.Stmt (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
def cfg (q : Q) (v : Option Symbol) (p a s c rows : List Symbol) : C :=
 ⟨some q,v,ContextProgram.storage p a s c rows⟩
def embed (c : WitnessParser.D) : C := ⟨c.l.map Q.axiom,c.var,c.stk⟩

def machine : Q → S
 | .uncons .nonempty => .goto (fun _ => .begin)
 | .uncons .empty => .goto (fun _ => .finish)
 | .uncons .reject => .goto (fun _ => .reject)
 | .uncons q => Routine.relocate ContextProgram.constructRoles Q.uncons (ContextUncons.machine q)
 | .begin => .peek .program (fun _ x => x)
   (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .reject))
    (.goto (fun _ => .axiom (.run (.dispatch .start)))))
 | .axiom .accept => .goto (fun _ => .uncons .tag0)
 | .axiom .reject => .goto (fun _ => .reject)
 | .axiom q => Routine.relocate id Q.axiom (WitnessParser.machine q)
 | .finish => .pop .program (fun _ x => x)
   (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .accept)) (.goto (fun _ => .reject)))
 | .accept | .reject => .halt

def codes (ws : List ZFR.ExecutableZF.AxiomWitness) := ws.flatMap (fun w => payloadBits (ZFR.TokenVM.emitWitness w))
def Matches : List ZFR.ExecutableZF.AxiomWitness → ZFR.Context → Prop
 | [],[] => True
 | w::ws,f::Γ => ZFR.ExecutableZF.axiomFormula w = some f ∧ Matches ws Γ
 | _,_ => False

theorem agree_uncons (q : ContextUncons.Control) (h : ContextUncons.machine q ≠ .halt) :
 machine (.uncons q) = Routine.relocate ContextProgram.constructRoles Q.uncons (ContextUncons.machine q) := by
 cases q <;> simp_all [machine,ContextUncons.machine]
theorem agree_axiom (q : WitnessParser.Q) (h : WitnessParser.machine q ≠ .halt) :
 machine (.axiom q) = Routine.relocate id Q.axiom (WitnessParser.machine q) := by
 cases q <;> simp_all [machine,WitnessParser.machine]

theorem embed_uncons (q : ContextUncons.Control) (v : Option Symbol) (p a s c rows : List Symbol) :
 Routine.embed ContextProgram.constructRoles Q.uncons (Segment.config q v a s c)
  (ContextProgram.storage p [] [] [] rows) = cfg (.uncons q) v p a s c rows := by
 unfold Routine.embed Segment.config cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem related_eq {c : WitnessParser.D} {d : C} (h : Routine.Related id Q.axiom c d) : d = embed c := by
 rcases c with ⟨l,v,T⟩
 rcases d with ⟨l',v',T'⟩
 rcases h with ⟨hl,hv,hT⟩
 change l' = l.map Q.axiom at hl
 change v' = v at hv
 change T' = T at hT
 subst l'; subst v'; subst T'
 rfl

theorem lift_axiom {c d : WitnessParser.D} (h : TM2.Reaches WitnessParser.machine c d) (hd : d.l ≠ none) :
 TM2.Reaches machine (embed c) (embed d) := by
 obtain ⟨d',hr,hrel,_⟩ := Routine.lift_run id Function.injective_id Q.axiom
  WitnessParser.machine machine agree_axiom h hd (show Routine.Related id Q.axiom c (embed c) from ⟨rfl,rfl,rfl⟩)
 rw [related_eq hrel] at hr
 exact hr

theorem embed_cfg (q : WitnessParser.Q) (v : Option Symbol) (p a s c rows : List Symbol) :
 embed (WitnessParser.cfg q v p a s c rows) = cfg (.axiom q) v p a s c rows := rfl

theorem uncons_nonempty (f : ZFR.Formula) (Γ : ZFR.Context) (v : Option Symbol) (p a rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.uncons .tag0) v p (TypedContext.value (.context (f::Γ)) ++ a) [] [] rows)
  (cfg .begin none p (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ a) [] [] rows) := by
 have h0 := Routine.lift_embedded_run ContextProgram.constructRoles ContextProgram.construct_injective Q.uncons
  ContextUncons.machine machine agree_uncons (ContextProgram.storage p [] [] [] rows)
  (ContextUncons.uncons_nonempty f Γ v a []) (by simp [Segment.config])
 simp only [embed_uncons] at h0
 have h1 : TM2.Reaches machine
  (cfg (.uncons .nonempty) none p (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ a) [] [] rows)
  (cfg .begin none p (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ a) [] [] rows) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 h1 ⊢
 exact h0.trans h1

theorem witness_nonempty (w : ZFR.ExecutableZF.AxiomWitness) :
 ∃ x xs, payloadBits (ZFR.TokenVM.emitWitness w) = x::xs ∧ x ≠ .frameEnd := by
 have hn : ZFR.TokenVM.emitWitness w ≠ [] := by
  cases w <;> simp [ZFR.TokenVM.emitWitness,ZFR.TokenVM.emitNat]
 obtain ⟨n,ns,he⟩ := List.exists_cons_of_ne_nil hn
 have hbits : tokenBits n ≠ [] := by simp [tokenBits]
 obtain ⟨x,xs,hx⟩ := List.exists_cons_of_ne_nil hbits
 refine ⟨x,xs ++ payloadBits ns,?_,?_⟩
 · simp [he,payloadBits,hx,List.flatMap_cons]
 · exact tokenBits_no_end n x (by rw [hx]; simp)

theorem begin_witness (w : ZFR.ExecutableZF.AxiomWitness) (v : Option Symbol) (p a rows : List Symbol) :
 ∃ reg, TM2.Reaches machine
  (cfg .begin v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) a [] [] rows)
  (cfg (.axiom (.run (.dispatch .start))) reg (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) a [] [] rows) := by
 obtain ⟨x,xs,hx,hne⟩ := witness_nonempty w
 refine ⟨some x,Relation.ReflTransGen.single ?_⟩
 rw [hx]
 cases x <;> simp_all [machine,cfg,TM2.step,TM2.stepAux,ContextProgram.storage]

theorem advance (w : ZFR.ExecutableZF.AxiomWitness) (f : ZFR.Formula) (Γ : ZFR.Context)
 (hf : ZFR.ExecutableZF.axiomFormula w = some f) (s : List ZFR.TokenVM.Value)
 (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.uncons .tag0) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack (.context (f::Γ) :: s)) [] [] rows)
  (cfg (.uncons .tag0) (some .frameEnd) p (TypedContext.stack (.context Γ :: s)) [] [] rows) := by
 have h0 := uncons_nonempty f Γ v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack s) rows
 obtain ⟨reg,h1⟩ := begin_witness w none p (TypedContext.stack (.formula f :: .context Γ :: s)) rows
 have h2 := lift_axiom (WitnessParser.accepts w f hf (.context Γ :: s) reg p rows) (by simp [WitnessParser.cfg])
 simp only [embed_cfg] at h2
 have h3 : TM2.Reaches machine
  (cfg (.axiom .accept) (some .frameEnd) p (TypedContext.stack (.context Γ :: s)) [] [] rows)
  (cfg (.uncons .tag0) (some .frameEnd) p (TypedContext.stack (.context Γ :: s)) [] [] rows) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at h0 h1 h2 h3 ⊢
 exact h0.trans (h1.trans (h2.trans h3))

theorem empty (v : Option Symbol) (p a rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.uncons .tag0) v (.frameEnd::p) (TypedContext.value (.context []) ++ a) [] [] rows)
  (cfg .accept (some .frameEnd) p a [] [] rows) := by
 have h0 := Routine.lift_embedded_run ContextProgram.constructRoles ContextProgram.construct_injective Q.uncons
  ContextUncons.machine machine agree_uncons (ContextProgram.storage (.frameEnd::p) [] [] [] rows)
  (ContextUncons.uncons_empty v a []) (by simp [Segment.config])
 simp only [embed_uncons] at h0
 have h1 : TM2.Reaches machine (cfg (.uncons .empty) (some .frameEnd) (.frameEnd::p) a [] [] rows)
  (cfg .finish (some .frameEnd) (.frameEnd::p) a [] [] rows) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine (cfg .finish (some .frameEnd) (.frameEnd::p) a [] [] rows)
  (cfg .accept (some .frameEnd) p a [] [] rows) := Relation.ReflTransGen.single (by
   simp [machine,cfg,TM2.step,TM2.stepAux,ContextProgram.storage]
   funext j; cases j <;> rfl)
 exact h0.trans (h1.trans h2)

theorem accepts (ws : List ZFR.ExecutableZF.AxiomWitness) (Γ : ZFR.Context) (h : Matches ws Γ)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.uncons .tag0) v (codes ws ++ .frameEnd::p) (TypedContext.stack (.context Γ :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := by
 induction ws generalizing Γ v with
 | nil =>
  cases Γ with
  | nil => exact empty v p (TypedContext.stack s) rows
  | cons f Γ => exact False.elim h
 | cons w ws ih =>
  cases Γ with
  | nil => exact False.elim h
  | cons f Γ =>
   have h0 := advance w f Γ h.1 s v (codes ws ++ .frameEnd::p) rows
   have h1 := ih Γ h.2 (some .frameEnd)
   simpa only [TM2.Reaches,codes,List.flatMap_cons,List.append_assoc] using h0.trans h1

def RejectTrace (start : C) (rows : List Symbol) : Prop :=
 ∃ v p a c, TM2.Reaches machine start (cfg .reject v p a [] c rows)

theorem reject_head (w : ZFR.ExecutableZF.AxiomWitness) (f : ZFR.Formula) (Γ : ZFR.Context)
 (hf : ZFR.ExecutableZF.axiomFormula w ≠ some f) (s : List ZFR.TokenVM.Value)
 (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.uncons .tag0) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p)
  (TypedContext.stack (.context (f::Γ) :: s)) [] [] rows) rows := by
 have h0 := uncons_nonempty f Γ v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack s) rows
 obtain ⟨reg,h1⟩ := begin_witness w none p (TypedContext.stack (.formula f :: .context Γ :: s)) rows
 obtain ⟨v',p',a',c',hr⟩ := WitnessParser.rejects w f hf (.context Γ :: s) reg p rows
 have h2 := lift_axiom hr (by simp [WitnessParser.cfg])
 simp only [embed_cfg] at h2
 have h3 : TM2.Reaches machine (cfg (.axiom .reject) v' p' a' [] c' rows)
  (cfg .reject v' p' a' [] c' rows) := Relation.ReflTransGen.single rfl
 refine ⟨v',p',a',c',?_⟩
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at h0 h1 h2 h3 ⊢
 exact h0.trans (h1.trans (h2.trans h3))

theorem reject_missing (f : ZFR.Formula) (Γ : ZFR.Context) (s : List ZFR.TokenVM.Value)
 (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.uncons .tag0) v (.frameEnd::p)
  (TypedContext.stack (.context (f::Γ) :: s)) [] [] rows) rows := by
 have h0 := uncons_nonempty f Γ v (.frameEnd::p) (TypedContext.stack s) rows
 have h1 : TM2.Reaches machine
  (cfg .begin none (.frameEnd::p) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows)
  (cfg .reject (some .frameEnd) (.frameEnd::p) (TypedContext.stack (.formula f :: .context Γ :: s)) [] [] rows) := by
  apply Relation.ReflTransGen.single
  simp [machine,cfg,TM2.step,TM2.stepAux,ContextProgram.storage]
 refine ⟨some .frameEnd,.frameEnd::p,TypedContext.stack (.formula f :: .context Γ :: s),[],?_⟩
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at h0 h1 ⊢
 exact h0.trans h1

theorem reject_extra (w : ZFR.ExecutableZF.AxiomWitness) (s : List ZFR.TokenVM.Value)
 (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.uncons .tag0) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p)
  (TypedContext.stack (.context [] :: s)) [] [] rows) rows := by
 obtain ⟨x,xs,hx,hne⟩ := witness_nonempty w
 have h0 := Routine.lift_embedded_run ContextProgram.constructRoles ContextProgram.construct_injective Q.uncons
  ContextUncons.machine machine agree_uncons (ContextProgram.storage (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) [] [] [] rows)
  (ContextUncons.uncons_empty v (TypedContext.stack s) []) (by simp [Segment.config])
 simp only [embed_uncons] at h0
 have h1 : TM2.Reaches machine
  (cfg (.uncons .empty) (some .frameEnd) (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack s) [] [] rows)
  (cfg .finish (some .frameEnd) (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack s) [] [] rows) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine
  (cfg .finish (some .frameEnd) (payloadBits (ZFR.TokenVM.emitWitness w) ++ p) (TypedContext.stack s) [] [] rows)
  (cfg .reject (some x) (xs ++ p) (TypedContext.stack s) [] [] rows) := by
  apply Relation.ReflTransGen.single
  rw [hx]
  cases x <;> simp_all [machine,cfg,TM2.step,TM2.stepAux,ContextProgram.storage]
  all_goals funext k; cases k <;> rfl
 exact ⟨some x,xs++p,TypedContext.stack s,[],h0.trans (h1.trans h2)⟩

theorem rejects (ws : List ZFR.ExecutableZF.AxiomWitness) (Γ : ZFR.Context) (h : ¬Matches ws Γ)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.uncons .tag0) v (codes ws ++ .frameEnd::p)
  (TypedContext.stack (.context Γ :: s)) [] [] rows) rows := by
 induction ws generalizing Γ v with
 | nil =>
  cases Γ with
  | nil => exact False.elim (h trivial)
  | cons f Γ => exact reject_missing f Γ s v p rows
 | cons w ws ih =>
  cases Γ with
  | nil => simpa only [codes,List.flatMap_cons,List.append_assoc] using reject_extra w s v (codes ws ++ .frameEnd::p) rows
  | cons f Γ =>
   by_cases hf : ZFR.ExecutableZF.axiomFormula w = some f
   · have ht : ¬Matches ws Γ := by intro hh; exact h ⟨hf,hh⟩
     obtain ⟨v',p',a',c',hr⟩ := ih Γ ht (some .frameEnd)
     have h0 := advance w f Γ hf s v (codes ws ++ .frameEnd::p) rows
     refine ⟨v',p',a',c',?_⟩
     simpa only [TM2.Reaches,codes,List.flatMap_cons,List.append_assoc] using h0.trans hr
   · simpa only [codes,List.flatMap_cons,List.append_assoc] using reject_head w f Γ hf s v (codes ws ++ .frameEnd::p) rows

theorem halted_labels (q : Q) (hq : machine q = .halt) (v : Option Symbol) (p a c rows : List Symbol)
 {d : C} (h : TM2.Reaches machine (cfg q v p a [] c rows) d) : d.l = some q ∨ d.l = none := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨b,hb,hbd⟩
 · exact Or.inl (congrArg TM2.Cfg.l he).symm
 · have hs : TM2.step machine (cfg q v p a [] c rows) = some ⟨none,v,ContextProgram.storage p a [] c rows⟩ := by
    simp [cfg,TM2.step,hq,TM2.stepAux]
   have he : b = ⟨none,v,ContextProgram.storage p a [] c rows⟩ := Option.some.inj (hb.symm.trans hs)
   subst b
   exact Or.inr (congrArg TM2.Cfg.l (Routine.dead_reaches machine rfl hbd))

theorem accepts_iff (ws : List ZFR.ExecutableZF.AxiomWitness) (Γ : ZFR.Context)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.uncons .tag0) v (codes ws ++ .frameEnd::p) (TypedContext.stack (.context Γ :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) ↔ Matches ws Γ := by
 constructor
 · intro ha
   by_contra hn
   obtain ⟨v',p',a',c',hr⟩ := rejects ws Γ hn s v p rows
   have hu : Relator.RightUnique (fun a b : C => TM2.step machine a = some b) := by
    intro a b c hab hac
    exact Option.some.inj (hab.symm.trans hac)
   rcases Relation.ReflTransGen.total_of_right_unique hu hr ha with h | h
   · rcases halted_labels .reject rfl v' p' a' c' rows h with he | he
     all_goals simp [cfg] at he
   · rcases halted_labels .accept rfl (some .frameEnd) p (TypedContext.stack s) [] rows h with he | he
     all_goals simp [cfg] at he
 · exact fun h => accepts ws Γ h s v p rows

end RosserDirect.WitnessContextCheck
