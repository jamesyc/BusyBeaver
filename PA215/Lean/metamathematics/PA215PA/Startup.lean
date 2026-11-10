import PA215PA.Startup.Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! Exact finite startup of the fixed dense215 table. The complete relative
binary tape is retained; this is not a nonhalting or clean-register theorem. -/
namespace PA215.PA.Startup

/-- All 63228 transitions are checked against the actual literal table. -/
theorem blank_run_63228 : NatTape.run 63228 NatTape.blank = some c064 := by
  have h0 : NatTape.run 8000 c000 = some c008 := part0
  have h1 : NatTape.run 16000 c000 = some c016 :=
    @NatTape.run_trans 8000 8000 c000 c008 c016 h0 part1
  have h2 : NatTape.run 24000 c000 = some c024 :=
    @NatTape.run_trans 16000 8000 c000 c016 c024 h1 part2
  have h3 : NatTape.run 32000 c000 = some c032 :=
    @NatTape.run_trans 24000 8000 c000 c024 c032 h2 part3
  have h4 : NatTape.run 40000 c000 = some c040 :=
    @NatTape.run_trans 32000 8000 c000 c032 c040 h3 part4
  have h5 : NatTape.run 48000 c000 = some c048 :=
    @NatTape.run_trans 40000 8000 c000 c040 c048 h4 part5
  have h6 : NatTape.run 56000 c000 = some c056 :=
    @NatTape.run_trans 48000 8000 c000 c048 c056 h5 part6
  have h7 : NatTape.run 63228 c000 = some c064 :=
    @NatTape.run_trans 56000 7228 c000 c056 c064 h6 part7
  exact h7

theorem final_control : c064.control = some ⟨81, by decide⟩ := rfl

theorem final_left : c064.left = 1 := rfl

theorem final_right :
    c064.right = 137125379776767170179580765213114232692120930255577756685319461 := rfl

/-- Transfer to the independently defined functional, bi-infinite tape.
`Rel` identifies every relative tape cell, not just a bounded window. -/
theorem functional_startup :
    ∃ c, PA215.run 63228 PA215.blank = some c ∧ NatTape.Rel c064 c :=
  NatTape.run_simulates 63228 NatTape.blank_rel blank_run_63228

#print axioms blank_run_63228
#print axioms functional_startup
end PA215.PA.Startup
