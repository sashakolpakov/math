import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopOuterTapeAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopOuterTapeMoments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafIncidenceOuterCarried

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried
open ProgramTapeReplay

/-- The actual assignment never reads or writes the outer tapes320/322/332. -/
theorem assignment : AvoidsCmd hidden Factor.assignment :=
  FactorLoop.OuterTape.assignment incidence_caller

/-- The complete sparse moments assembly and dense readout avoid those tapes. -/
theorem denseCommand : AvoidsCmd hidden (MomentsAssembly.denseCommand Factor.assignment) :=
  FactorLoop.OuterTape.denseCommand Factor.assignment assignment

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
