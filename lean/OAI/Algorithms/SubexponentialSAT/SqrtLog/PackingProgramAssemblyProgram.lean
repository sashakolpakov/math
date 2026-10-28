import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyHeads
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyFinalize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidatesBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramRefinement

namespace OAI.Algorithms

/-! One fixed finite command for the weighted packing-score producer.
Every candidate loop, prefix operation, and arithmetic operation is a linked
finite bit program; all varying data live on runtime stacks. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev command : Cmd 16 48 := .seq incidence (.seq heads weightAndMerge)
def program := compiled command 8 0

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
