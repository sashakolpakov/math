import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsStage
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteMomentPhase

namespace OAI.Algorithms

/-!
# Installing the concrete jobs and moment stages in the node loop

Only the unfinished cache/template producers and the per-exponent source
constructor remain parameters. Job enumeration and the dense arithmetic
moment phase below are the actual finite programs owned by their modules.
This factory alone does not discharge their data-layout trace contracts.
-/

namespace SubexponentialSAT.SubexpNodeMomentPipeline

open BitProgram StructuredCalls
open SubexpNodeMomentLoop (Stage)

/-- Taylor preparation has finished before dense execution, so its current
node register is physically emptied before the moment-phase workspace check. -/
abbrev phaseCommand : Cmd 16 256 :=
  .seq (.call (StackRoutines.clearProgram 78 0 1))
    (.seq (.call (StackRoutines.clearProgram 116 0 1))
      (.call (ProgramLinking.liftProgram SubexpConcreteMomentPhase.program id (Fin.castAdd 128))))

abbrev phaseProgram : Program 16 256 (size phaseCommand + 1) := compiled phaseCommand 100 102

def phaseStage : Stage := ⟨_, phaseProgram⟩

def jobsStage (sourceService : SubexpOuterJobs.Code) : Stage :=
  ⟨_, SubexpNodeJobsStage.masterProgram sourceService⟩

/-- Every node calls the actual master-stream jobs adapter and the actual
concrete dense moment phase. The table is independent of Q, D and all data. -/
def worker (cache template : Stage) (sourceService : SubexpOuterJobs.Code) :=
  SubexpNodeMomentLoop.pipelineProgram cache template (jobsStage sourceService) phaseStage

def program (cache template : Stage) (sourceService : SubexpOuterJobs.Code) :=
  SubexpNodeMomentLoop.program (worker cache template sourceService)

end SubexponentialSAT.SubexpNodeMomentPipeline

end OAI.Algorithms
