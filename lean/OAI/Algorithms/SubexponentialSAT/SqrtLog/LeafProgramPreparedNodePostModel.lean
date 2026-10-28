import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeReachableNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePadding

namespace OAI.Algorithms

/-! Fixed per-node frame and storage interfaces for the actual collector.
They do not depend on an individual native execution witness. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes
open PreparedSource NodeNative LeafHeadSetupProgram

variable {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)

def storageCap (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q) : ℕ :=
  NodeEnvelope.queryStorageCap query k occurrence qi hg p.firstWord p.remainingWords node
    (Query.Width.incomingWidth p)

def collectorFrame (occurrence qi : ℕ) (hv : query.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
    (node : Fin (Query.packingProblem query k hg).Q) (high : List Bool)
    (frame : Fin 768 → List Bool) : Prop :=
  let q := fixedSpec p hv source hsource node
  let A := storageCap p occurrence qi node
  FactorLoop.AssignmentFrame q (List.replicate ((numeric query k p.lengths).val 34) true)
    (FactorResource.sourceCap q A A A) A A A LeafStatisticsProgram.Arity.decoded
    q.p.ops.zeroRun.1 q.p.ops.oneRun.1 query.forward
    (HighIncidenceProgram.Restriction.zeroMerge query.forward.reverse high).reverse
    (FactorLoop.maskedHigh frame)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost

end

end OAI.Algorithms
