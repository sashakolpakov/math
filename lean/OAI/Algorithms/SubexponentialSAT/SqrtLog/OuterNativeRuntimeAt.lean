import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeKernels

namespace OAI.Algorithms

/-! One input-independent query budget, specialized uniformly to every
actual origin and optional mark reached by a single outer leaf. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT ProducedQueryResources

structure RuntimeAt (n k B qi X Q : ℕ) : Prop where
  marked : ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q=n → Origin q k B → q.clauses.length ≤ n*B →
    queryBytes q ≤ X → RuntimeFacts q k B qi (markedCoefficient k) (markedExponent k) ∧
      queryLimit k qi (markedCoefficient k) (markedExponent k) q ≤ Q
  accepted : ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q=n → Origin q k B → q.clauses.length ≤ n*B →
    queryBytes q ≤ X → RuntimeFacts q k B qi (acceptedCoefficient k) (acceptedExponent k) ∧
      queryLimit k qi (acceptedCoefficient k) (acceptedExponent k) q ≤ Q

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
