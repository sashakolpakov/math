import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoaderCore

/-! The fixed loader call shared by the tuple syntax and its proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open BitProgram StructuredCalls

/-- The stack address holding the DFS's current physical head. -/
def headAddress : Fin 896 := 845

/-- The DFS always requests its current physical head. -/
def loadHead : Cmd 40 896 := .call (SignatureHeadLoader.programFrom headAddress)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
