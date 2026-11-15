module
public import PrimitiveMPField
public import PrimitiveMPCopy
public import PrimitiveMPGuard
public import PrimitiveConsCore
public import PrimitivePushBindings
@[expose] public section
namespace C209Search.Primitive.MP
open M209.Source
def registers (t w d h l : Nat) (f : Registers) : Registers := fun r =>
  if r = 2 then t else if r = 0 then w else if r = 3 then d else if r = 7 then h
  else if r = 1 then l else if r = 8 ∨ r = 5 then 0 else f r

def config (pc t w d h l : Nat) (f : Registers) : Configuration :=
  ⟨pc,registers t w d h l f⟩

theorem push_registers (t w d h l : Nat) (f : Registers) :
    PairCore.registers ⟨t,w,0,0,registers 0 0 d h l f⟩ = registers t w d h l f := by
  funext r
  by_cases h1 : r = 2 <;> by_cases h2 : r = 0 <;> by_cases h4 : r = 3 <;>
    by_cases h5 : r = 7 <;> by_cases h8 : r = 1 <;>
    by_cases h6 : r = 8 <;> by_cases h7 : r = 5 <;>
    simp_all [PairCore.registers,registers]

theorem field_registers (t w d h l : Nat) (f : Registers) :
    MPField.registers ⟨l,d,0,0,registers t w 0 h 0 f⟩ = registers t w d h l f := by
  funext r
  by_cases h1 : r = 2 <;> by_cases h2 : r = 0 <;> by_cases h4 : r = 3 <;>
    by_cases h5 : r = 7 <;> by_cases h8 : r = 1 <;>
    by_cases h6 : r = 8 <;> by_cases h7 : r = 5 <;>
    simp_all [MPField.registers,registers]

theorem copy_registers (t w d h l : Nat) (f : Registers) :
    MPCopy.registers d t 0 (registers 0 w 0 h l f) = registers t w d h l f := by
  funext r
  by_cases h1 : r = 2 <;> by_cases h2 : r = 0 <;> by_cases h4 : r = 3 <;>
    by_cases h5 : r = 7 <;> by_cases h8 : r = 1 <;>
    by_cases h6 : r = 8 <;> by_cases h7 : r = 5 <;>
    simp_all [MPCopy.registers,registers]

theorem guard_registers (t w d h l : Nat) (f : Registers) :
    MPGuard.registers t h 0 (registers 0 w d 0 l f) = registers t w d h l f := by
  funext r
  by_cases h1 : r = 2 <;> by_cases h2 : r = 0 <;> by_cases h4 : r = 3 <;>
    by_cases h5 : r = 7 <;> by_cases h8 : r = 1 <;>
    by_cases h6 : r = 8 <;> by_cases h7 : r = 5 <;>
    simp_all [MPGuard.registers,registers]


private theorem cons_pair_bound : PairCore.Bound 4273 := by unfold PairCore.Bound; decide +kernel
private theorem cons_times_bound : TimesFour.Bound 4283 := by unfold TimesFour.Bound; decide +kernel
private theorem constructor (t w : Nat) (f : Registers) :
 ∃ n, 0<n ∧ Steps n (PairCore.configAt 4262 0 ⟨t,w,0,0,f⟩)
 (PairCore.configAt 4262 27 ⟨C209Soundness.impCode (M6.Source.Cantor.decode w).1 t,(M6.Source.Cantor.decode w).2,0,0,f⟩) :=
 ConsCore.cons PopCore.mp_bound cons_pair_bound cons_times_bound t w f
/-- Actual MP push/copy/constructor prefix, keeping the decoded offset D.
The stack is restored after extracting the just-pushed antecedent. -/
theorem pre_guard (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4236 t w d h l f)
      (config 4289 (C209Soundness.impCode t d) w d h l f) := by
  obtain ⟨np,hp,sp⟩ := Push.push Push.bound_4236 t w (registers 0 0 d h l f)
  have a : Steps np (config 4236 t w d h l f)
      (config 4255 0 (M6.Source.Cantor.pair t w) d h l f) := by
    simpa only [Push.configAt,PairCore.configAt,push_registers,config,Nat.reduceAdd] using sp
  have b : Steps (7*d+2) (config 4255 0 (M6.Source.Cantor.pair t w) d h l f)
      (config 4262 d (M6.Source.Cantor.pair t w) d h l f) := by
    simpa only [MPCopy.config,copy_registers,Nat.zero_add,config,Nat.reduceAdd]
      using MPCopy.first_copy d 0 (registers 0 (M6.Source.Cantor.pair t w) 0 h l f)
  obtain ⟨nc,hc,sc⟩ := constructor d (M6.Source.Cantor.pair t w) (registers 0 0 d h l f)
  have c : Steps nc (config 4262 d (M6.Source.Cantor.pair t w) d h l f)
      (config 4289 (C209Soundness.impCode t d) w d h l f) := by
    simpa only [PairCore.configAt,push_registers,M6.Source.Cantor.decode_pair,config,Nat.reduceAdd] using sc
  exact ⟨np+(7*d+2)+nc,by omega,steps_trans (steps_trans a b) c⟩

/-- Field decode through the actual equality decision. The only remaining
successful branch is the zero-push and D restoration after ordinal3884. -/
theorem to_guard_result (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4222 t w d h l f)
      (config (if C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1) = h then 4302 else 4328)
        0 w (d+(M6.Source.Cantor.decode l).1) 0 (M6.Source.Cantor.decode l).2 f) := by
  have sf := MPField.unpair_add l d (registers t w 0 h 0 f)
  have a : Steps (MPField.loopCost l (0,0)+(3*(M6.Source.Cantor.decode l).2+1)+(3*(M6.Source.Cantor.decode l).1+1)) (config 4222 t w d h l f)
      (config 4236 t w (d+(M6.Source.Cantor.decode l).1) h (M6.Source.Cantor.decode l).2 f) := by
    simpa only [MPField.configAt,MPField.exitAt,field_registers,config] using sf
  obtain ⟨np,hp,sp⟩ := pre_guard t w (d+(M6.Source.Cantor.decode l).1) h (M6.Source.Cantor.decode l).2 f
  obtain ⟨ng,hg,sg⟩ := MPGuard.guard (C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1)) h
    (registers 0 w (d+(M6.Source.Cantor.decode l).1) 0 (M6.Source.Cantor.decode l).2 f)
  have c : Steps ng
      (config 4289 (C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1)) w
        (d+(M6.Source.Cantor.decode l).1) h (M6.Source.Cantor.decode l).2 f)
      (config (if C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1) = h then 4302 else 4328)
        0 w (d+(M6.Source.Cantor.decode l).1) 0 (M6.Source.Cantor.decode l).2 f) := by
    simpa only [MPGuard.config,guard_registers,config] using sg
  exact ⟨_,by omega,steps_trans (steps_trans a sp) c⟩


private theorem return_row : program 4328 = some (.jump 25) := by decide +kernel
theorem return_to_fetch (t w d h l : Nat) (f : Registers) :
 Steps 1 (config 4328 t w d h l f) (config 25 t w d h l f) := by
 apply Steps.cons
 have hs : step (config 4328 t w d h l f) = config 25 t w d h l f := by
  unfold step scalarNext config
  rw [return_row]
  rfl
 rw [hs]
 exact Steps.refl _
theorem success (w d l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4302 0 w d 0 l f)
      (config 25 d (M6.Source.Cantor.pair 0 w) d 0 l f) := by
  obtain ⟨np,hp,sp⟩ := Push.push Push.bound_4302 0 w (registers 0 0 d 0 l f)
  have a : Steps np (config 4302 0 w d 0 l f)
      (config 4321 0 (M6.Source.Cantor.pair 0 w) d 0 l f) := by
    simpa only [Push.configAt,PairCore.configAt,push_registers,config,Nat.reduceAdd] using sp
  have b : Steps (7*d+2) (config 4321 0 (M6.Source.Cantor.pair 0 w) d 0 l f)
      (config 4328 d (M6.Source.Cantor.pair 0 w) d 0 l f) := by
    simpa only [MPCopy.config,copy_registers,Nat.zero_add,config,Nat.reduceAdd]
      using MPCopy.last_copy d 0 (registers 0 (M6.Source.Cantor.pair 0 w) 0 0 l f)
  exact ⟨np+(7*d+2)+1,by omega,steps_trans (steps_trans a b) (return_to_fetch _ _ _ _ _ _)⟩

/-- COMPLETE actual MP macro4222–4328. It consumes the offset field, tests
I(T,D+offset)=H, and implements both success and failure stack effects. All
unrelated registers are preserved, X=Y=H=0 at return to actual source ordinal25.
No macro-correctness or arithmetic interpreter assumption is used. -/
theorem command (t w d h l : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n (config 4222 t w d h l f)
      (config 25
        (if C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1) = h then d+(M6.Source.Cantor.decode l).1 else 0)
        (if C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1) = h then M6.Source.Cantor.pair 0 w else w)
        (d+(M6.Source.Cantor.decode l).1) 0 (M6.Source.Cantor.decode l).2 f) := by
  obtain ⟨np,hp,sp⟩ := to_guard_result t w d h l f
  by_cases hc : C209Soundness.impCode t (d+(M6.Source.Cantor.decode l).1) = h
  · simp only [hc,↓reduceIte] at sp ⊢
    obtain ⟨ns,hs,ss⟩ := success w (d+(M6.Source.Cantor.decode l).1) (M6.Source.Cantor.decode l).2 f
    exact ⟨np+ns,by omega,steps_trans sp ss⟩
  · simp only [hc,↓reduceIte] at sp ⊢
    exact ⟨np+1,by omega,steps_trans sp (return_to_fetch _ _ _ _ _ _)⟩

/-- The command interface with an explicitly encoded next operand field. -/
theorem command_field (t w d h x tail : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps n
      (config 4222 t w d h (M6.Source.Cantor.pair x tail) f)
      (config 25 (if C209Soundness.impCode t (d+x) = h then d+x else 0)
        (if C209Soundness.impCode t (d+x) = h then M6.Source.Cantor.pair 0 w else w)
        (d+x) 0 tail f) := by
  simpa only [M6.Source.Cantor.decode_pair] using command t w d h (M6.Source.Cantor.pair x tail) f


/-- Real partial execution, not only totalized-step reachability. -/
theorem run_command_field (t w d h x tail : Nat) (f : Registers) :
 ∃ n, 0<n ∧ runSource n (config 4222 t w d h (M6.Source.Cantor.pair x tail) f) = some
 (config 25 (if C209Soundness.impCode t (d+x)=h then d+x else 0)
 (if C209Soundness.impCode t (d+x)=h then M6.Source.Cantor.pair 0 w else w)
 (d+x) 0 tail f) := by
 obtain ⟨n,hn,hs⟩ := command_field t w d h x tail f
 refine ⟨n,hn,steps_real _ _ _ hs ?_⟩
 have row : program 25 = some (.dec 1 27 26) := by decide +kernel
 unfold scalarNext config
 rw [row]
 simp only [Option.bind_some,scalarExecute]
 repeat split <;> simp_all
end C209Search.Primitive.MP
