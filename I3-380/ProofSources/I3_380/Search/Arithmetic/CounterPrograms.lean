module
public import I3_380.Search.Arithmetic.ProgramRuns
public import I3_380.Search.Compiler.Source
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_decrement_zero {s : Store M} {r : Register} (zero : s r = 0) :
    (dec r).Runs (.escape 0) s.code s.code := by
  simpa only [dec,Op.effect,zero,↓reduceIte] using Program.Runs.instruction (.decNZ r) s

theorem coded_decrement_positive {s : Store M} {r : Register} (nonzero : s r ≠ 0) :
    (dec r).Runs .normal s.code (s.set r (s r-1)).code := by
  simpa only [dec,Op.effect,nonzero,↓reduceIte] using Program.Runs.instruction (.decNZ r) s

theorem coded_increment (r : Register) (s : Store M) :
    (inc r).Runs .normal s.code (s.set r (s r+1)).code :=
  Program.Runs.instruction (.inc r) s

theorem coded_continue (n : Nat) (s : Store M) :
    (continue_ n).Runs (.repeatAt n) s.code s.code :=
  Program.Runs.instruction (.continue_ n) s

private theorem drain_prefix (r : Register) (body : Program) (states : M → Store M) (count : M)
    (definition : 𝚺ᴬ₁-Function₁ (fun i => (states i).code))
    (atStep : ∀ i < count, states i r ≠ 0 ∧
      body.Runs (.repeatAt 0) ((states i).set r (states i r-1)).code (states (i+1)).code)
    {final : M} (rest : (Program.seq (dec r) body).Runs .normal (states count).code final) :
    (Program.seq (dec r) body).Runs .normal (states 0).code final := by
  let edge := fun a b : M => ∃ middle, (dec r).Runs .normal a middle ∧ body.Runs (.repeatAt 0) middle b
  have instructions : ∀ i < count, edge (states i).code (states (i+1)).code := by
    intro i before
    obtain ⟨nonzero,loops⟩ := atStep i before
    exact ⟨_,coded_decrement_positive nonzero,loops⟩
  have trace := Chain.ofFunction edge (fun i => (states i).code) definition count instructions
  obtain ⟨steps,ending,tail,result⟩ := rest
  exact ⟨count+steps,ending,trace.trans tail,result⟩

theorem coded_while_done (r : Register) (body : Program) (s : Store M) (zero : s r = 0) :
    (whilePositive r body).Runs .normal s.code s.code :=
  Program.Runs.leftExit (coded_decrement_zero zero) rfl

theorem coded_while_more {r : Register} {body : Program} {s mid t : Store M} (nonzero : s r ≠ 0)
    (first : body.Runs .normal (s.set r (s r-1)).code mid.code)
    (rest : (whilePositive r body).Runs .normal mid.code t.code) :
    (whilePositive r body).Runs .normal s.code t.code :=
  Program.Runs.reenter (coded_decrement_positive nonzero)
    (Program.Runs.rightExit first (coded_continue 1 mid) rfl) rest

/-- Validate an arbitrary model-finite prefix of a counter loop using
its register invariant. The suffix can exit or continue separately. -/
theorem coded_while_prefix (r : Register) (body : Program) (states : M → Store M) (count : M)
    (definition : 𝚺ᴬ₁-Function₁ (fun i => (states i).code))
    (atStep : ∀ i < count, states i r ≠ 0 ∧
      body.Runs .normal ((states i).set r (states i r-1)).code (states (i+1)).code)
    {final : M} (rest : (whilePositive r body).Runs .normal (states count).code final) :
    (whilePositive r body).Runs .normal (states 0).code final := by
  apply drain_prefix r (.seq body (continue_ 1)) states count definition _ rest
  intro i before
  obtain ⟨nonzero,executes⟩ := atStep i before
  exact ⟨nonzero,Program.Runs.rightExit executes (coded_continue 1 _) rfl⟩

theorem coded_while (r : Register) (body : Program) (states : M → Store M) (count : M)
    (definition : 𝚺ᴬ₁-Function₁ (fun i => (states i).code)) (done : states count r = 0)
    (atStep : ∀ i < count, states i r ≠ 0 ∧
      body.Runs .normal ((states i).set r (states i r-1)).code (states (i+1)).code) :
    (whilePositive r body).Runs .normal (states 0).code (states count).code :=
  coded_while_prefix r body states count definition atStep (coded_while_done r body _ done)

theorem coded_clear (r : Register) (s : Store M) :
    (clear r).Runs .normal s.code (s.set r 0).code := by
  let states := fun i : M => s.set r (s r-i)
  have definition : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
    have update := Store.writeCode_definable (M := M) r
    have codeAt (i : M) : (states i).code = Store.writeCode r s.code (s r-i) := by
      simp [states,Store.writeCode]
    simp only [codeAt]
    definability
  have done : states (s r) r = 0 := by simp [states]
  have base : states 0 = s := by simp [states,Store.set_same]
  have finish : states (s r) = s.set r 0 := by simp [states]
  have stopped : (clear r).Runs .normal (states (s r)).code (states (s r)).code :=
    Program.Runs.leftExit (coded_decrement_zero done) rfl
  suffices steps : _ by
    simpa only [base,finish,clear] using drain_prefix r (continue_ 0) states (s r) definition steps stopped
  intro i before
  have remaining : 0 < s r-i := Arithmetic.pos_sub_iff_lt.mpr before
  refine ⟨by simpa only [states,Store.get_set] using remaining.ne',?_⟩
  have next : (states i).set r (states i r-1) = states (i+1) := by
    simp [states,Store.set_set,Arithmetic.sub_sub]
  rw [next]
  exact coded_continue 0 _

def increase (targets : List Register) (s : Store M) (amount : M) : Store M :=
  fun r => if r ∈ targets then s r + amount else s r

theorem coded_increase (targets : List Register) (distinct : targets.Nodup) (s : Store M) :
    (block (targets.map inc)).Runs .normal s.code (increase targets s 1).code := by
  induction targets generalizing s with
  | nil => exact Program.Runs.instruction (.break_ 0) s
  | cons r rest ih =>
    obtain ⟨notUsed,tailDistinct⟩ := List.nodup_cons.mp distinct
    let next := s.set r (s r+1)
    have result : increase (r::rest) s 1 = increase rest next 1 := by
      funext i
      by_cases same : i = r
      · subst i
        simp [increase,notUsed,next]
      · simp [increase,next,same,Store.get_set_other]
    cases rest with
    | nil =>
      rw [result]
      exact coded_increment r s
    | cons q qs =>
      rw [result]
      exact Program.Runs.rightExit (coded_increment r s) (ih tailDistinct next) rfl

/-- Transfer a unary counter to any fixed list of distinct destinations.
The same invariant supplies both the move and the two-output copy loop. -/
theorem coded_transfer (source : Register) (targets : List Register)
    (different : source ∉ targets) (distinct : targets.Nodup) (s : Store M) :
    (whilePositive source (block (targets.map inc))).Runs .normal s.code
      ((increase targets s (s source)).set source 0).code := by
  let states := fun i : M => (increase targets s i).set source (s source-i)
  have definition : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
    apply matrixToVec_definable₁
    intro r
    by_cases same : r = source
    · simp only [states,Store.set,same,↓reduceIte]
      definability
    · by_cases member : r ∈ targets
      · simp only [states,Store.set,increase,same,member,↓reduceIte]
        definability
      · simp only [states,Store.set,increase,same,member,↓reduceIte]
        definability
  have done : states (s source) source = 0 := by simp [states]
  have base : states 0 = s := by
    funext r
    by_cases same : r = source <;> simp [states,increase,Store.set,same]
  have finish : states (s source) = (increase targets s (s source)).set source 0 :=
    by simp [states]
  have trace := coded_while source (block (targets.map inc)) states (s source) definition done
  suffices steps : _ by
    simpa only [base,finish] using trace steps
  intro i before
  have available : 0 < s source-i := Arithmetic.pos_sub_iff_lt.mpr before
  let next := (states i).set source (states i source-1)
  have result : increase targets next 1 = states (i+1) := by
    funext r
    by_cases same : r = source
    · subst r
      simp [next,states,increase,different,Arithmetic.sub_sub]
    · simp only [states,next,increase,Store.set,same,↓reduceIte]
      by_cases member : r ∈ targets <;> simp [member,add_assoc]
  exact ⟨by simpa only [states,Store.get_set] using available.ne',
    by simpa only [result] using coded_increase targets distinct next⟩

theorem coded_move {a b : Register} (different : a ≠ b) (s : Store M) :
    (move a b).Runs .normal s.code ((s.set a 0).set b (s b+s a)).code := by
  have final : (increase [b] s (s a)).set a 0 = (s.set a 0).set b (s b+s a) := by
    funext r
    by_cases ra : r = a <;> by_cases rb : r = b <;> simp_all [increase,Store.set]
  simpa [move,block,final,different] using coded_transfer a [b] (by simpa using different) (by simp) s

theorem coded_copy {a b : Register} (ab : a ≠ b) (au : a ≠ u) (bu : b ≠ u) (s : Store M)
    (zeroScratch : s u = 0) :
    (copy a b).Runs .normal s.code (s.set b (s b+s a)).code := by
  let stage := (increase [b,u] s (s a)).set a 0
  have spread : (whilePositive a (.seq (inc b) (inc u))).Runs .normal s.code stage.code :=
    coded_transfer a [b,u] (by simp [ab,au]) (by simp [bu]) s
  have restore := coded_move (Ne.symm au) stage
  have final : (stage.set u 0).set a (stage a+stage u) = s.set b (s b+s a) := by
    funext r
    by_cases ra : r = a <;> by_cases rb : r = b <;> by_cases ru : r = u <;>
      simp_all [stage,increase,Store.set,Ne.symm ab,Ne.symm au,Ne.symm bu]
  rw [final] at restore
  exact Program.Runs.rightExit spread restore rfl

end PalomarI3380.Compiler.Source
