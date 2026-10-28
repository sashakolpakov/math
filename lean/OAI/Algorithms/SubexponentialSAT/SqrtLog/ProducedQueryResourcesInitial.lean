import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform

namespace OAI.Algorithms

/-! Fixed exponents for every actual live leaf of the executed dyadic splitter.
The original ambient variable set is retained throughout. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter SAT Asymptotic
open scoped Topology

/-- The actual occurrence parameter, rather than an independently supplied
polylog bound, is eventually bounded by one fixed power of L. -/
theorem initial_occurrence_bound (k T : ℕ) :
    ∃ qi : ℕ, ∀ᶠ n : ℕ in atTop,
      SparsifyDyadic.occurrenceBound k T (s n) ≤ L n^qi := by
  obtain ⟨q,hq⟩ := SparsifyBounds.occurrence_le_log_power k T
  refine ⟨2*q,?_⟩
  filter_upwards [eventually_L_ge 2] with n hn
  have hh : L n+2 ≤ L n^2 := by nlinarith
  calc
    _ ≤ (L n+2)^q := hq n
    _ ≤ (L n^2)^q := Nat.pow_le_pow_left hh q
    _ = L n^(2*q) := (pow_mul _ _ _).symm

/-- Simultaneous initial fields for every actual live leaf, including the
clause-count bound used by code setup and all selector trials. -/
theorem initial_leaf_bounds (k T : ℕ) :
    ∃ qi : ℕ, ∀ᶠ n : ℕ in atTop, ∀ F : CNF (Fin n), WidthAtMost k F →
      ∀ G ∈ SparsifyDyadic.liveLeaves k T (s n) F,
      WidthAtMost k G ∧
      G.card ≤ n*SparsifyDyadic.occurrenceBound k T (s n) ∧
      SparsifyDyadic.occurrenceBound k T (s n) ≤ L n^qi ∧
      (0 < G.card → 0 < SparsifyDyadic.occurrenceBound k T (s n)) := by
  obtain ⟨qi,hqi⟩ := initial_occurrence_bound k T
  refine ⟨qi,?_⟩
  filter_upwards [hqi] with n hn F hF G hG
  obtain ⟨hw,_,hc⟩ := SparsifyDyadic.liveLeaves_spec k T (s n) F hF G hG
  refine ⟨hw,hc,hn,?_⟩
  intro hpos
  by_contra h
  have hz : SparsifyDyadic.occurrenceBound k T (s n)=0 := by omega
  simp only [hz,Nat.mul_zero] at hc
  omega

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
