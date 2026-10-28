import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyGuards
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramPositivity

namespace OAI.Algorithms

/-! Instantiate the uniform guard theorem with the actual measured scope
statistics.  Only the retained-half and scope-size estimates remain as
upstream obligations; positivity and neutral coverage are derived here. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafParametersProgram

def measuredArity (scopes : List (List ℕ)) (mask : List Bool) : ℕ :=
  max (Arity.arity mask scopes 0)
    (if (measured scopes mask).uncovered = 0 then 0 else 1)

def measuredParameterInput (scopes : List (List ℕ)) (mask : List Bool)
    (clauses width : ℕ) : Input :=
  { ambient := mask.length
    freeCount := (measured scopes mask).free
    clauses := clauses
    width := width
    factors := scopes.length + (measured scopes mask).uncovered
    occurrence := (measured scopes mask).occurrence
    arity := measuredArity scopes mask
    incidences := (measured scopes mask).incidences }

theorem eventually_measured_guards (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (mask : List Bool)
      (clauses width : ℕ),
      mask.length = n → n ≤ 2*(measured scopes mask).free →
      0 < clauses → (∀ row ∈ scopes, row.Nodup) →
      (measured scopes mask).occurrence ≤ C*Asymptotic.L n^q →
      measuredArity scopes mask ≤ C*Asymptotic.L n^q →
      Guard (measuredParameterInput scopes mask clauses width) := by
  filter_upwards [eventually_parameter_guards_ambient C q,
    eventually_ge_atTop (2 : ℕ)] with n hn hnpos scopes mask clauses width
      hlen hhalf hcl hnodup hB ha
  have hfree : 0 < (measured scopes mask).free := by omega
  exact hn (measuredParameterInput scopes mask clauses width) hlen
    ((free_le_ambient scopes mask).trans_eq hlen) hhalf hcl
    (occurrence_pos_of_free_pos scopes mask hfree)
    (arity_pos_of_free_pos scopes mask hnodup hfree)
    (free_le_incidences scopes mask) hB ha

theorem measured_guards_uniform_cutoff (C q : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (scopes : List (List ℕ)) (mask : List Bool)
      (clauses width : ℕ),
      mask.length = n → n ≤ 2*(measured scopes mask).free →
      0 < clauses → (∀ row ∈ scopes, row.Nodup) →
      (measured scopes mask).occurrence ≤ C*Asymptotic.L n^q →
      measuredArity scopes mask ≤ C*Asymptotic.L n^q →
      let x := measuredParameterInput scopes mask clauses width
      Guard x ∧ passes x = true ∧ dispatch x = .sparse := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (eventually_measured_guards C q)
  refine ⟨N,?_⟩
  intro n hn scopes mask clauses width hlen hhalf hcl hnodup hB ha
  have h := hN n hn scopes mask clauses width hlen hhalf hcl hnodup hB ha
  exact ⟨h,(passes_eq_true _).2 h,(dispatch_sparse_iff _).2 h⟩

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
