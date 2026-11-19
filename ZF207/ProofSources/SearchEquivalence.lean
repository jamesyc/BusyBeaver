module
public import SearchCompiler
public import SearchScheduler
@[expose] public section
namespace C207Search
open C207Soundness

/-- The retained-store arithmetic scheduler refutes exactly the numeric source
calculus, from its clean initial store and first candidate2. This is NOT yet
the literal primitive-source scheduler theorem. -/
theorem retained_scheduler_iff_refutation :
 SequentialSearchHalts 2 zeroStore ↔ ExactProvable 1 := by
 constructor
 · intro h
   exact sequential_search_refutes 2 zeroStore zero_sound h
 · intro h
   obtain ⟨cs,hcs⟩ := refutation_has_uniform_ax_word h
   exact uniform_ax_word_search 0 0 0 cs hcs zeroStore
end C207Search
