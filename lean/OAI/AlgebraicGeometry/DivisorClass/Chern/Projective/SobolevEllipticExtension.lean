import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.SobolevCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.CoefficientExtension

/-! # Sobolev Elliptic Extension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! At every actual bundle chart point, the Fourier-normalized native principal coefficient has a bounded smooth Lipschitz extension with proved integrated coercivity. -/

open _root_.TopologicalSpace _root_.MeasureTheory Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient_exists_elliptic_extension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
        GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n,
      A =ᶠ[𝓝 z] h.projectiveLineSobolevCoefficient V e n i ∧ ContDiff ℝ ∞ A ∧
      HasCompactSupport (fun x => A x - h.projectiveLineSobolevCoefficient V e n i z) ∧
      (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L A) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ y : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
        ∀ v : Lp (GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
          (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        c * ‖v‖ ^ 2 ≤ ∫ x, inner ℝ (A (x + y) (v x)) (v x) := by
  have H := h.projectiveLineSobolevCoefficient_uniform_lower V e he n i
    (isCompact_singleton (x := z)) (Set.singleton_subset_iff.mpr hz)
  let c := H.choose
  have hc : 0 < c := H.choose_spec.1
  have hpos : ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (h.projectiveLineSobolevCoefficient V e n i z v) v :=
    H.choose_spec.2 z (Set.mem_singleton z)
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  have HE := Positive.CoefficientExtension.exists_positive_coefficient_extension D.isOpen (h.projectiveLineSobolevCoefficient V e n i)
    (h.projectiveLineSobolevCoefficient_smooth V e he n i) hz c hc hpos
  let A := HE.choose
  have ha := HE.choose_spec
  refine ⟨A, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, c / 2, half_pos hc, fun y v => ?_⟩
  exact Positive.CoefficientExtension.positive_coefficient_translated_integral A ha.2.1.continuous
    ha.2.2.2.1.choose (c / 2) ha.2.2.2.1.choose_spec ha.2.2.2.2.2 y v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
