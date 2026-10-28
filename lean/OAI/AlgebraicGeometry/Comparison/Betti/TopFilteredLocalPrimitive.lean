import OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredForms
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalPoincare

/-! # Top Filtered Local Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredLocalPrimitive.Hodge

noncomputable section

/-! Closed forms in the top smooth filtration have actual local
holomorphic primitives, in every lower allowed filtration. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalPoincare

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem topFiltered_local_primitive (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1))
    (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) ((n + 1 : ℕ) : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ u : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, u ∈ Open.FiltrationDescent.Hodge.openFormFiltration V n r ∧
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  obtain ⟨A, hA, hAd⟩ := TopFilteredForms.Hodge.closed_topFiltered_holomorphic U (n + 1) a ha hd
  obtain ⟨V, hV, hxV, b, hb⟩ := Holomorphic.LocalPoincare.local_primitive_on U A hAd x
  refine ⟨V, hxV, hV, Holomorphic.LocalDescent.ambientHolomorphicInclusion V n b,
    Holomorphic.FilteredSections.Hodge.ambientHolomorphicInclusion_filtered E M V n r hr b, ?_⟩
  rw [TopFilteredForms.Hodge.ambientHolomorphicInclusion_d, hb, ← Holomorphic.LocalDescent.ambientHolomorphicInclusion_restrict, hA]

end

end OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredLocalPrimitive.Hodge
