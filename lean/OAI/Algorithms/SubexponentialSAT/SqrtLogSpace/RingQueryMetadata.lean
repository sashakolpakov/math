import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSource

/-! The actual query frontend links its addressed head node count to the
numeric bank. The generic native factor construction is independent of this
frontend execution closure. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram.PreparedSource

/-- The authentic addressed head input and the actual numeric bank use the
same node count; the input padding does not alter this value. -/
theorem actual_heads_node_count (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem q k hg).Q) (l : Fin 8 → ℕ) :
    (heads q k hg first tail node).Q = (numeric q k l).val 21 :=
  (numeric_Q q k l).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
