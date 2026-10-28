import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorReconstruction

/-! # Vector Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.VectorCoefficients

noncomputable section

/-! The full actual chart coefficient field is smooth over the complex scalars. -/

open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ}

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem form_coefficients_holomorphic (a : DeRhamComplex.forms E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    ContDiffOn ℂ ∞ ((DeRhamComplex.inclusion E M n a).val.inChart e) e.target := by
  classical
  let b := Module.finBasis ℂ E
  let F := (DeRhamComplex.inclusion E M n a).val.inChart e
  have hc : ContDiffOn ℂ ∞ (fun y => Pure.CovectorReconstruction.Holomorphic.rawCovectorCoordinates b n (F y)) e.target := by
    apply contDiffOn_pi.mpr
    intro v
    exact ScalarCoefficients.form_scalarCoefficient_holomorphic a e he (fun i => b (v i))
  have hR : ContDiff ℂ ∞ (Pure.CovectorReconstruction.Holomorphic.pureCovectorReconstruction b n) :=
    ContinuousLinearMap.contDiff _
  have hS : ContDiff ℂ ∞ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).subtypeL :=
    ContinuousLinearMap.contDiff _
  have hr := hR.comp_contDiffOn hc
  have hs := hS.comp_contDiffOn hr
  apply hs.congr
  intro y hy
  exact (Pure.CovectorReconstruction.Holomorphic.pureCovectorProjection_eq_self b n (F y)
    (a.val.hasBidegree_inChart e he hy)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.VectorCoefficients
