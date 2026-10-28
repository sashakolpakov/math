import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec

namespace OAI.Algorithms

/-! The count returned by the concrete prepared query is exactly the outer
selector count, both for the unmarked query and for each marked clause. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram LeafOuterProgram LeafParametersProgram
noncomputable section
attribute [local irreducible] Execute.guardedModel

 theorem fixedSpec_selectorCount {n B : ℕ}
    (F : Formula n) (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width : ℕ) (hm : 0 < (formulaRecords F).length) (payloads : List (List Bool))
    (mark : Option (Fin (formulaRecords F).length)) (k : ℕ)
    {initial : Factor.Data}
    {hg : Guard ((query F a (payloadRows F width hm payloads) mark).input k)}
    {W V L : ℕ}
    (p : Query.Preparation (query F a (payloadRows F width hm payloads) mark) k initial hg W V L)
    (hv : (query F a (payloadRows F width hm payloads) mark).Valid)
    (node : Fin (Query.packingProblem (query F a (payloadRows F width hm payloads) mark) k hg).Q) :
    let N := (Query.packingProblem (query F a (payloadRows F width hm payloads) mark) k hg).n
    let source := querySource F a ha (payloadRows F width hm payloads) mark N rfl
    let spec := PreparedSource.fixedSpec p hv source
      (querySource_bytes F a ha (payloadRows F width hm payloads) mark N rfl) node
    PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause =
      selectorCount F width payloads mark := by
  dsimp only
  let source := querySource F a ha (payloadRows F width hm payloads) mark
    (Query.packingProblem (query F a (payloadRows F width hm payloads) mark) k hg).n rfl
  let spec := PreparedSource.fixedSpec p hv source
    (querySource_bytes F a ha (payloadRows F width hm payloads) mark _ rfl) node
  exact factorSpec_selectorCount F a ha width hm payloads mark rfl hv
    spec.p spec.ps spec.packing spec.J spec.hJ spec.theta spec.width spec.widthLength spec.code

end
end SubexponentialSAT.SqrtLog.OuterQuery.Count

end OAI.Algorithms
