import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp

/-! # Schwartz -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz

noncomputable section

/-! The already constructed original compact frame coefficients as genuine vector-valued Schwartz functions. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def holomorphicLineFrameCoefficientsSchwartz : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) where
  toFun a := (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_compact V u e i n f hf hs a).toSchwartzMap
    (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_smooth V u e he i n f hf hs a)
  map_add' a b := by
    apply DFunLike.ext
    intro z
    exact congrFun ((CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs).map_add a b) z
  map_smul' g a := by
    apply DFunLike.ext
    intro z
    exact congrFun ((CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs).map_smul g a) z

theorem holomorphicLineFrameCoefficientsSchwartz_coe (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (holomorphicLineFrameCoefficientsSchwartz V e he i n f hf hs a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) =
      CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a := rfl

theorem holomorphicLineFrameCoefficientsSchwartz_toLp (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (holomorphicLineFrameCoefficientsSchwartz V e he i n f hf hs a).toLp 2 volume =
      CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i n f hf hs a := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz
