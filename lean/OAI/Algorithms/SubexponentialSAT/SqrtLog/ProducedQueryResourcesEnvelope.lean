import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesFinal

namespace OAI.Algorithms

/-! The constructed resource has the uniform target bound for every fixed
native-envelope power. A measured execution bound must still be supplied by
the caller that composes the actual native traces. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem eventually_resourceEnvelope (k qi power ordinaryPower : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        (nativeEnvelope k n power ordinaryPower (resources q k B qi hg a tail):ℝ) ≤
          (18:ℝ)^power*(2:ℝ)^((1+(power:ℝ)*
            exponentConstant k (LeafScopeResourceBounds.resourceExponent qi+1))*Statement.runtimeScale n) := by
  filter_upwards [eventually_resources_bounds k qi,
    eventually_nativeEnvelope_bound k qi (LeafScopeResourceBounds.resourceExponent qi+1)
      (9*ordinaryExponent+8) power ordinaryPower]
    with n hres henv q B hv hqn o hB hc hBL hg a tail haN haC
  exact henv _ ((hres q B hv hqn o hB hc hBL).2.2 hg a tail haN haC)

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
