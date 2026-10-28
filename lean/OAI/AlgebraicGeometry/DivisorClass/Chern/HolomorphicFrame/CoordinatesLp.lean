import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.ChartOn
import OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity

/-! # Coordinates Lp -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp

noncomputable section

/-! Literal compact frame coefficients of the original bundle forms as Euclidean L² classes. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def holomorphicLineFrameCoefficientLinear : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  (Analysis.HodgeTheory.Decomposition.CoefficientLinearity.Constructions.supportedCoefficientLinear V e n).comp
    ((Analysis.DifferentialForms.Manifold.Algebra.smoothManifoldFormSubmodule V.analyticModel V.analyticSpace n).subtype.comp
      (ChartOn.holomorphicLineChartFrameTestLinear V e i n f hf hs))

include he in
theorem holomorphicLineFrameCoefficients_memLp (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    MemLp (holomorphicLineFrameCoefficientLinear V e i n f hf hs a) 2 volume :=
  (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_smooth V u e he i n f hf hs a).continuous.memLp_of_hasCompactSupport
    (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_compact V u e i n f hf hs a)

def holomorphicLineFrameCoefficientsLp : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
    Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) where
  toFun a := (holomorphicLineFrameCoefficients_memLp V e he i n f hf hs a).toLp
    (holomorphicLineFrameCoefficientLinear V e i n f hf hs a)
  map_add' a b := by
    rw [← MemLp.toLp_add (holomorphicLineFrameCoefficients_memLp V e he i n f hf hs a)
      (holomorphicLineFrameCoefficients_memLp V e he i n f hf hs b)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun ((holomorphicLineFrameCoefficientLinear V e i n f hf hs).map_add a b))
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (holomorphicLineFrameCoefficients_memLp V e he i n f hf hs a)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun ((holomorphicLineFrameCoefficientLinear V e i n f hf hs).map_smul c a))

theorem holomorphicLineFrameCoefficientsLp_norm_sq (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖holomorphicLineFrameCoefficientsLp V e he i n f hf hs a‖ ^ 2 =
      ∫ z, ‖Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a).val z‖ ^ 2 :=
  Analysis.HodgeTheory.Decomposition.CoordinateLp.Constructions.memLp_toLp_norm_sq _ (holomorphicLineFrameCoefficients_memLp V e he i n f hf hs a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoordinatesLp
