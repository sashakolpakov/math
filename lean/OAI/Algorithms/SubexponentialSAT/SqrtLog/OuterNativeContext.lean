import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeAccepted

namespace OAI.Algorithms

/-! The remaining concrete residual interface, with exactly the fixed native
node constants. This record is consumed by native query execution, never by a
machine instruction. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram

structure PreparedCountContext {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Query.Data}
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k initial hg W V L) (base : Query.Data)
    (count B qi : ℕ) where
  budget : ℕ
  width : ℕ
  execution : Marked.Wide.BranchContext Residual.command
    (Marked.Wide.maskCopied (Query.prepared p.out))
    (Query.ProtectedWork (Query.Carried.reference base)) count budget width
  step : execution.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap p B qi)
    (Query.Cost.nodeCap p B qi Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
      Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
  stepWidth : execution.stepWidth ≤ Query.Cost.ordinaryCap p B qi
  referenceBound : execution.referenceBound ≤ Query.Cost.ordinaryCap p B qi

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
