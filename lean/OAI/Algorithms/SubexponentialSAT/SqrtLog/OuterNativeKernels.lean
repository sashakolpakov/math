import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQueryContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostNode

namespace OAI.Algorithms

/-! Width-dependent native query coefficients selected once, before the
ambient dimension or any input. Commands remain the already compiled finite
marked/accepted programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT LeafProgram Filter
open scoped Topology

 def markedCoefficient (k : ℕ) : ℕ := Classical.choose
  (marked_contract_of_polynomial k Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
    Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
 def markedExponent (k : ℕ) : ℕ := Classical.choose (Classical.choose_spec
  (marked_contract_of_polynomial k Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
    Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent))
 theorem markedKernel (k : ℕ) : type_of% (Classical.choose_spec (Classical.choose_spec
    (marked_contract_of_polynomial k Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
      Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent))) :=
  Classical.choose_spec (Classical.choose_spec
    (marked_contract_of_polynomial k Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
      Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent))

 def acceptedCoefficient (k : ℕ) : ℕ := Classical.choose (Query.Cost.accepted_fixed_polynomial k)
 def acceptedExponent (k : ℕ) : ℕ := Classical.choose (Classical.choose_spec
  (Query.Cost.accepted_fixed_polynomial k))
 theorem acceptedKernel (k : ℕ) : type_of% (Classical.choose_spec (Classical.choose_spec
    (Query.Cost.accepted_fixed_polynomial k))) :=
  Classical.choose_spec (Classical.choose_spec (Query.Cost.accepted_fixed_polynomial k))

 theorem eventually_kernel_runtime (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : LeafQueryFrontend.Query) (B : ℕ),
      q.Valid → ProducedQueryResources.ambient q=n → ProducedQueryResources.Origin q k B →
      0 < B → q.clauses.length ≤ n*B → B ≤ Asymptotic.L n^qi →
      RuntimeFacts q k B qi (markedCoefficient k) (markedExponent k) ∧
      RuntimeFacts q k B qi (acceptedCoefficient k) (acceptedExponent k) := by
  filter_upwards [eventually_runtimeFacts k qi (markedCoefficient k) (markedExponent k),
    eventually_runtimeFacts k qi (acceptedCoefficient k) (acceptedExponent k)]
    with n hm ha q B hv hn ho hB hc hBL
  exact ⟨hm q B hv hn ho hB hc hBL,ha q B hv hn ho hB hc hBL⟩

end SubexponentialSAT.SqrtLog.OuterNativeServices

end

end OAI.Algorithms
