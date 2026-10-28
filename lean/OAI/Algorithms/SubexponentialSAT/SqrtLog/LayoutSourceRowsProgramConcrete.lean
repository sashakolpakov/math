import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramController
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramStaging

namespace OAI.Algorithms

/-! The actual finite source-row controller. This is a fixed composition of
native plan lookup, source dispatch, polynomial execution and row emission. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def sourceRow : Code := sourceRowWith stagedPackedSource

/-- The lookup's retained register4 reports actual pair membership. Missing
factor incidences produce a complete ambient zero-row table. Caller parks the
four target-cutoff caches before entry and restores them after exit; the full
source cutoff is always read from210. -/
def sourceRows : Code := sourceRowsWith stagedPackedSource

def sourceRowsProgram := compiled sourceRows 337 205

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
