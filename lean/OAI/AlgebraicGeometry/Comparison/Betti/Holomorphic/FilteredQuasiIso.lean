import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Above
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Boundary

/-! # Filtered Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredQuasiIso.Hodge

noncomputable section

/-! The original brutally truncated holomorphic de Rham complex maps
quasi-isomorphically to the independently constructed smooth Hodge filtration. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicFilteredSheafMap_quasiIso (r : ℤ) : QuasiIso (FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) := by
  apply (quasiIso_iff _).mpr
  intro n
  by_cases hbelow : (n : ℤ) < r
  · exact Filtered.Below.Hodge.holomorphicFilteredSheafMap_quasiIsoAt_below E M r n hbelow
  · have hr : r ≤ (n : ℤ) := le_of_not_gt hbelow
    cases n with
    | zero => exact Filtered.ComparisonZero.Hodge.holomorphicFilteredSheafMap_quasiIsoAt_zero E M r hr
    | succ n =>
        by_cases habove : r ≤ (n : ℤ)
        · exact Filtered.Above.Hodge.holomorphicFilteredSheafMap_quasiIsoAt_above E M r n habove
        · have he : r = ((n + 1 : ℕ) : ℤ) := by omega
          rw [he]
          exact Filtered.Boundary.Hodge.holomorphicFilteredSheafMap_quasiIsoAt_boundary E M n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredQuasiIso.Hodge
