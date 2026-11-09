module

public import PA215.Source.CommandTransfer
public import PA215.Source.SchedulerInvariantCore

@[expose] public section
namespace PA215.Source.Scheduler
/-- Actual literal-source scheduler safety; every source macro supplier has
been proved against the exact source, including the complete actual AX Plan. -/
theorem source_scheduler_nonhalting (h : ArithmeticSafe) :
    ¬ CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) :=
  scheduler_nonhalting_of_transfer parsed_command_step h
#print axioms source_scheduler_nonhalting
end PA215.Source.Scheduler
