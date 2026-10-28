import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

noncomputable section

/-! The fixed accepted-head path first constructs the actual ambient assignment,
then evaluates its selected factor records, adds the resulting dense array to
the head accumulator, and reclaims the arithmetic environment. Zero-valued and
empty factor products follow the same addition/reset path. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

/-- This concrete command has no callback or evaluator parameter. -/
def accepted : HeadSumProgram.Code :=
  .seq HighQueryAdapter.NativeOverlay.prepare
    (.seq FactorAssignmentProgram.assignment HeadSumProgram.accumulate)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram

/-- One fixed head rescan includes entry cleanup, every candidate, and final
counter cleanup. Its dimensions and parameters are read from physical words. -/
def program := HeadSumAssembly.headProgram HeadSumAssembly.accepted

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram

end
