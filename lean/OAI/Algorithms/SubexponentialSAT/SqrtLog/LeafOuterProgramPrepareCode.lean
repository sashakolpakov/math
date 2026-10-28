import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Numerical preparation followed by physical cleanup of the entire worker bank. -/
abbrev prepareHash : Cmd 40 896 :=
  .seq LeafProgram.HashParameters.command clearWorker

/-- Preserve the exact, possibly padded, count-word width for later row decoding. -/
abbrev saveWidth : Cmd 40 896 := route (768,783)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
