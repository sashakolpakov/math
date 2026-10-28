import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramRow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitializeLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupFound
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramZero

namespace OAI.Algorithms

/-! Fixed outer control, parameterized only by a finite native source command.
The concrete instantiation supplies the actual packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def sourceRowsWith (source : Code) : Code := .seq initializeSource
  (.seq LayoutSourcePlanLookup.Native.command
    (.seq (.ite 4 (rowsCommand (sourceRowWith source)) zeroRows) (clear 304)))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
