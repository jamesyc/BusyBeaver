# The I3-334 result

The standalone [Challenge](../ProofSources/I3_334/Challenge.lean) and
[Solution](../ProofSources/I3_334/Solution.lean) state and prove
`PalomarI3334.exactClaim` for the [literal table](../data/zfc-i3-native-334.tm).

- A closed set-theoretic sentence represents halting on the blank
  tape in every model of ZFC + I3.
- Syntactic consistency implies actual nonhalting and makes
  nonhalting unprovable in ZFC + I3. The external converse is formalized
  as `literal_nonhalting_iff_consistency`.
- Under arithmetic Σ₁-soundness, neither halting nor nonhalting is
  provable in ZFC + I3.

The [machine simulation](../ProofSources/I3_334/Simulation/MachineSimulation.lean)
identifies the exact blank-tape run with the compiled search. Its
[search proof](../ProofSources/I3_334/Search/SearchCompleteness.lean)
reduces halting to the existence of a derivation of `D = J` in the
ten guarded equations. The [calibration](../ProofSources/I3_334/Proof/Calibration.lean)
uses internally finite proof and machine traces to prove the
consistency implication needed for unprovability of nonhalting.
