module
public import SourceND
@[expose] public section
namespace ZFR
inductive Base : Row → Prop where
 | ctx {Γ a} : a ∈ Γ → Base (.seq Γ a)
 | pc (Γ a b) : Base (.seq Γ (.imp (.imp (.imp a b) a) a))
inductive Unary : Row → Row → Prop where
 | ii (Γ a b) : Unary (.seq (a::Γ) b) (.seq Γ (.imp a b))
 | exp (Γ a) : Unary (.seq Γ .bot) (.seq Γ a)
 | ce1 (Γ a b) : Unary (.seq Γ (.and a b)) (.seq Γ a)
 | ce2 (Γ a b) : Unary (.seq Γ (.and a b)) (.seq Γ b)
 | di1 (Γ a b) : Unary (.seq Γ a) (.seq Γ (.or a b))
 | di2 (Γ a b) : Unary (.seq Γ b) (.seq Γ (.or a b))
 | wk {Γ Δ} (a) : ContextSub Γ Δ → Unary (.seq Γ a) (.seq Δ a)
 | allI (Γ a) : Unary (.seq (shiftContext Γ) a) (.seq Γ (.all a))
 | allE (Γ a t) : Unary (.seq Γ (.all a)) (.seq Γ (subst t a))
 | exI (Γ a t) : Unary (.seq Γ (subst t a)) (.seq Γ (.ex a))
inductive Binary : Row → Row → Row → Prop where
 | ie (Γ a b) : Binary (.seq Γ (.imp a b)) (.seq Γ a) (.seq Γ b)
 | ci (Γ a b) : Binary (.seq Γ a) (.seq Γ b) (.seq Γ (.and a b))
 | branchPair (Γ a b c) : Binary (.seq (a::Γ) c) (.seq (b::Γ) c) (.branches Γ a b c)
 | de (Γ a b c) : Binary (.seq Γ (.or a b)) (.branches Γ a b c) (.seq Γ c)
 | exE (Γ a c) : Binary (.seq Γ (.ex a)) (.seq (a::shiftContext Γ) (shift c)) (.seq Γ c)

def Rule (r : Row) (xs : List Row) : Prop :=
 Base r ∨ (∃ p, p ∈ xs ∧ Unary p r) ∨ ∃ p q, p ∈ xs ∧ q ∈ xs ∧ Binary p q r
inductive Trace : List Row → Prop where
 | nil : Trace []
 | cons {r xs} : Rule r xs → Trace xs → Trace (r::xs)

theorem Rule.mono {r xs ys} (h : Rule r xs) (sub : ∀ a, a ∈ xs → a ∈ ys) : Rule r ys := by
 rcases h with hb | ⟨p,hp,hu⟩ | ⟨p,q,hp,hq,hb⟩
 · exact Or.inl hb
 · exact Or.inr (Or.inl ⟨p, sub p hp, hu⟩)
 · exact Or.inr (Or.inr ⟨p,q,sub p hp,sub q hq,hb⟩)

theorem Trace.append {xs ys} (h : Trace xs) (hy : Trace ys) : Trace (xs++ys) := by
 induction h with
 | nil => exact hy
 | cons hr ht ih =>
   exact Trace.cons (hr.mono (fun a ha => List.mem_append_left ys ha)) ih

theorem Base.sound {r} (h : Base r) : ND r := by
 cases h with
 | ctx hm => exact ND.ctx hm
 | pc Γ a b => exact ND.pc Γ a b

theorem Unary.sound {p r} (h : Unary p r) (hp : ND p) : ND r := by
 cases h with
 | ii => exact ND.ii hp
 | exp => exact ND.exp hp
 | ce1 => exact ND.ce1 hp
 | ce2 => exact ND.ce2 hp
 | di1 => exact ND.di1 hp
 | di2 => exact ND.di2 hp
 | wk a hs => exact ND.wk hs hp
 | allI => exact ND.allI hp
 | allE Γ a t => exact ND.allE t hp
 | exI Γ a t => exact ND.exI t hp

theorem Binary.sound {p q r} (h : Binary p q r) (hp : ND p) (hq : ND q) : ND r := by
 cases h with
 | ie => exact ND.ie hp hq
 | ci => exact ND.ci hp hq
 | branchPair => exact ND.branchPair hp hq
 | de => exact ND.de hp hq
 | exE => exact ND.exE hp hq

theorem Trace.sound {xs} (h : Trace xs) : ∀ r, r ∈ xs → ND r := by
 induction h with
 | nil => simp
 | @cons r xs hr ht ih =>
   intro a ha
   rcases List.mem_cons.mp ha with he | hm
   · subst a
     rcases hr with hb | ⟨p,hp,hu⟩ | ⟨p,q,hp,hq,hb⟩
     · exact hb.sound
     · exact hu.sound (ih p hp)
     · exact hb.sound (ih p hp) (ih q hq)
   · exact ih a hm

def HasTrace (r : Row) : Prop := ∃ xs, Trace xs ∧ r ∈ xs

theorem Base.hasTrace {r} (h : Base r) : HasTrace r :=
 ⟨[r], Trace.cons (Or.inl h) Trace.nil, List.mem_cons_self⟩

theorem Unary.hasTrace {p r} (h : Unary p r) (hp : HasTrace p) : HasTrace r := by
 obtain ⟨xs,hx,hm⟩ := hp
 exact ⟨r::xs, Trace.cons (Or.inr (Or.inl ⟨p,hm,h⟩)) hx, List.mem_cons_self⟩

theorem Binary.hasTrace {p q r} (h : Binary p q r) (hp : HasTrace p) (hq : HasTrace q) : HasTrace r := by
 obtain ⟨xs,hx,hm⟩ := hp
 obtain ⟨ys,hy,hn⟩ := hq
 exact ⟨r::(xs++ys), Trace.cons (Or.inr (Or.inr ⟨p,q,
   List.mem_append_left ys hm,List.mem_append_right xs hn,h⟩)) (hx.append hy), List.mem_cons_self⟩

theorem ND.hasTrace {r} (h : ND r) : HasTrace r := by
 induction h with
 | ctx hm => exact (Base.ctx hm).hasTrace
 | pc Γ a b => exact (Base.pc Γ a b).hasTrace
 | ii h ih => exact (Unary.ii ..).hasTrace ih
 | ie h1 h2 ih1 ih2 => exact (Binary.ie ..).hasTrace ih1 ih2
 | exp h ih => exact (Unary.exp ..).hasTrace ih
 | ci h1 h2 ih1 ih2 => exact (Binary.ci ..).hasTrace ih1 ih2
 | ce1 h ih => exact (Unary.ce1 ..).hasTrace ih
 | ce2 h ih => exact (Unary.ce2 ..).hasTrace ih
 | di1 h ih => exact (Unary.di1 ..).hasTrace ih
 | di2 h ih => exact (Unary.di2 ..).hasTrace ih
 | branchPair h1 h2 ih1 ih2 => exact (Binary.branchPair ..).hasTrace ih1 ih2
 | de h1 h2 ih1 ih2 => exact (Binary.de ..).hasTrace ih1 ih2
 | wk hs h ih => exact (Unary.wk _ hs).hasTrace ih
 | allI h ih => exact (Unary.allI ..).hasTrace ih
 | allE t h ih => exact (Unary.allE _ _ t).hasTrace ih
 | exI t h ih => exact (Unary.exI _ _ t).hasTrace ih
 | exE h1 h2 ih1 ih2 => exact (Binary.exE ..).hasTrace ih1 ih2

end ZFR
