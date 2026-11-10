import Lake

open System Lake DSL

package pa211Metamathematics where version := v!"0.1.0"

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation.git"@"c3eb37ae896dc8f1d239ba1511e74d9f25e9d158"

require pa211 from ".."

lean_lib PA215PA

lean_lib PA213PA

lean_lib PA211Endpoint where roots :=
  #[`User211CompleteModelCoverage, `User211ConsistentNonhalting, `User211EndpointExactHaltingFormula,
    `User211EndpointInternalCarryNatBridge, `User211EndpointInternalCodedSourceFrame,
    `User211EndpointInternalCodedSourcePhysicalStep, `User211EndpointInternalCodedSourcePhysicalTrace,
    `User211EndpointInternalFixedFile, `User211EndpointInternalFixedTraceSigma, `User211EndpointInternalScanNatBridge,
    `User211EndpointInternalStartupFrame, `User211EndpointInternalStartupHaltingBridge,
    `User211EndpointInternalStartupTrace, `User211EndpointInternalSymbolicGraphs,
    `User211EndpointInternalTraceProjection, `User211EndpointPaddedBridge, `User211EndpointPaddedNatTape,
    `User211EndpointPhysicalAdequacy, `User211EndpointSentenceCorrectness, `User211EndpointStartupData,
    `User211EndpointStartupSourceBinding, `User211EndpointTraceAdequacy, `User211EndpointZipNatTape,
    `User211InternalActualRefutationSentences, `User211LiteralArithmeticBinding, `User211LiteralEndpoint,
    `User211ModelCoverage, `User211ModelCoverage000, `User211ModelCoverage001, `User211ModelCoverage002,
    `User211ModelCoverage003, `User211ModelCoverage004, `User211ModelCoverage005, `User211ModelCoverage006,
    `User211ModelCoverage007, `User211ModelCoverage008, `User211ModelCoverage009, `User211ModelCoverage010,
    `User211ModelCoverage011, `User211ModelCoverage012, `User211ModelCoverage013, `User211ModelCoverage014,
    `User211ModelCoverage015, `User211ModelCoverage016, `User211ModelCoverage017, `User211ModelCoverage018,
    `User211ModelCoverage019, `User211ModelCoverage020, `User211ModelCoverage021, `User211ModelCoverage022,
    `User211ModelCoverage023, `User211ModelCoverage024, `User211ModelCoverage025, `User211ModelCoverage026,
    `User211ModelCoverage027, `User211ModelCoverage028, `User211ModelCoverage029, `User211ModelCoverage030,
    `User211ModelCoverage031, `User211ModelCoverage032, `User211ModelCoverage033, `User211ModelCoverage034,
    `User211ModelCoverage035, `User211ModelCoverage036, `User211ModelCoverage037, `User211ModelCoverage038,
    `User211ModelCoverage039, `User211ModelCoverage040, `User211ModelCoverage041, `User211ModelCoverage042,
    `User211ModelCoverage043, `User211ModelCoverage044, `User211ModelCoverage045, `User211ModelCoverage046,
    `User211ModelCoverage047, `User211ModelCoverage048, `User211ModelCoverage049, `User211ModelCoverage050,
    `User211ModelCoverage051, `User211ModelCoverage052, `User211ModelCoverage053, `User211ModelCoverage054,
    `User211ModelCoverage055, `User211ModelCoverage056, `User211ModelCoverage057, `User211ModelCoverage058,
    `User211ModelCoverage059, `User211ModelCoverage060, `User211ModelCoverage061, `User211ModelCoverageAssembler,
    `User211NonhaltingUnprovability, `User211PAHaltingFormula, `User211PAInternalCallAudit, `User211PAInternalCarryCell,
    `User211PAInternalCarryCode, `User211PAInternalCarryFile, `User211PAInternalCarryReturnRelation,
    `User211PAInternalDecrementPositive, `User211PAInternalDecrementPositiveCell, `User211PAInternalDecrementZero,
    `User211PAInternalDecrementZeroCell, `User211PAInternalFileBoxes, `User211PAInternalFileEffects,
    `User211PAInternalFileGraphs, `User211PAInternalFileGuards, `User211PAInternalFileLayout,
    `User211PAInternalForwardCell, `User211PAInternalForwardFile, `User211PAInternalIncrement,
    `User211PAInternalIncrementTail, `User211PAInternalLeftPhase, `User211PAInternalMarkAll,
    `User211PAInternalMarkDelimiter, `User211PAInternalMarkPrefix, `User211PAInternalMarkReturnGeneric,
    `User211PAInternalMarkSkipGeneric, `User211PAInternalNativeRows, `User211PAInternalOracleAlphabet,
    `User211PAInternalPhaseTrace, `User211PAInternalPhysicalFrame, `User211PAInternalPhysicalRegisters,
    `User211PAInternalReturnCell, `User211PAInternalReturnCode, `User211PAInternalReturnFile,
    `User211PAInternalRollbackCell, `User211PAInternalRollbackFile, `User211PAInternalRows,
    `User211PAInternalRunNormalization, `User211PAInternalScanBits, `User211PAInternalScanLeft,
    `User211PAInternalScanRight, `User211PAInternalSegmentCompose, `User211PAInternalSelectedCell,
    `User211PAInternalSymbolicAudit, `User211PAInternalSymbolicExec, `User211PAInternalSymbolicPeel,
    `User211PAInternalSymbolicPrimitives, `User211PAInternalSymbolicStep, `User211PAInternalSymbolicWords,
    `User211PAInternalTerminalContract, `User211PAInternalTrace, `User211PAInternalTraceAppend,
    `User211PAInternalTraceCompose, `User211PAInternalTracePrepend, `User211PAInternalTraceRows,
    `User211PAInternalUniformOracle, `User211PAMachine, `User211PAModelPrimitive, `User211PANatTape,
    `User211PANativeTable, `User211PAStepFormula, `User211PAStepSemantics, `User211PATape, `User211PATheory,
    `User211RefutationHalting, `User211SourceCalibration]

-- A fresh build can exhaust a hosted runner when several large certificates
-- elaborate together. Finish the proof imports in a one-worker Lake process
-- before this build schedules the Solution's imports.
target preparePA211Proofs pkg : Unit := do
  if (← IO.getEnv "PA211_BOUNDED_BUILD") == some "1" then
    return Job.nil
  let lake ← getLake
  Job.async do
    proc {
      cmd := lake.toString
      args := #["--quiet", "build", "PA211PA"]
      cwd := pkg.dir
      env := #[("LEAN_NUM_THREADS", some "1"), ("PA211_BOUNDED_BUILD", some "1")]
    } (quiet := true)

@[default_target] lean_lib PA211PA where
  extraDepTargets := #[`preparePA211Proofs]

lean_lib PA211PalomarSurface where
  roots := #[`Challenge, `PA211Statement]

lean_lib PA211Palomar where
  roots := #[`Solution]
  extraDepTargets := #[`preparePA211Proofs]
