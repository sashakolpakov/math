import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests

/-! # Test Scalar -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestScalar

noncomputable section

/-! Original frame extraction commutes with smooth scalar multiplication in the order required by chart reconstruction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineChartFrameTest_mul_right (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hsg : tsupport g ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction g hg (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hsf a) =
      Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n g hg hsg (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) := by
  apply Subtype.ext
  funext x
  change g x • Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hsf a x = _
  by_cases hx : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  · rw [Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_apply V u e i n f hf hsf a ⟨x, hx⟩,
      Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_apply V u e i n g hg hsg _ ⟨x, hx⟩,
      Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply]
  · rw [Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_zero V u e i n f hf hsf a x (fun ht => hx (hsf ht).2),
      Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_zero V u e i n g hg hsg _ x (fun ht => hx (hsg ht).2)]
    exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) (g x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestScalar
