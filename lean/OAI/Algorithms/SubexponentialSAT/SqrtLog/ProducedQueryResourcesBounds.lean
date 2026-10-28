import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesPacking
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankCertificate
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeadsQuery

namespace OAI.Algorithms

/-! Simultaneous Bounds for the actual query and searched packing. Neither
rank, head size, cardinalities of bucket tables, nor running times are
assumptions of this theorem. The alphabet premises describe the output of
the native complete-alphabet enumeration. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem rank_budget (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
    16*(layoutR (q.input k).freeCount:ℝ)*(L (q.input k).freeCount:ℝ)^2*
      (rank q k hg a tail:ℝ) ≤ (q.input k).freeCount :=
  ProducedQueryRank.query_rank_budget q k hg a tail haN haC

 theorem headSize_budget (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
    (headSize q k hg a tail:ℝ) ≤ 2*(ambient q:ℝ)/layoutR (q.input k).freeCount :=
  LayoutProducedHeads.query_max_bound_real q k hg a tail haN haC

/-- A single input-size cutoff works for all trials, marks, high branches,
searched complete alphabets, and physical padding. -/
 theorem eventually_ofPacking_bounds (k qi C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      LeafParametersProgram.Guard (q.input k) ∧ SmallInputs q k n ∧
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        CostAssembly.Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1) (9*e+8) n
          (ofPacking q k B C d qi e hg a tail) := by
  filter_upwards [eventually_make_bounds k qi C d e,eventually_small_inputs k qi]
    with n hbound hsmall q B hv hqn o hB hc hBL
  obtain ⟨hs,hinputs⟩ := hsmall q B hv hqn o hB hc hBL
  refine ⟨hs.guard,hinputs,?_⟩
  intro hg a tail haN haC
  apply hbound q B _ _ hv hqn o hB hc hBL
  · exact rank_budget q k hg a tail haN haC
  · simpa only [hqn] using headSize_budget q k hg a tail haN haC

 theorem ofPacking_uniform_cutoff (k qi C d e : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      LeafParametersProgram.Guard (q.input k) ∧ SmallInputs q k n ∧
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) →
        CostAssembly.Bounds qi (LeafScopeResourceBounds.resourceExponent qi+1) (9*e+8) n
          (ofPacking q k B C d qi e hg a tail) :=
  Filter.eventually_atTop.mp (eventually_ofPacking_bounds k qi C d e)

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
