import OAI.Analysis.HodgeTheory.Decomposition.RealMultiplier

/-! # Manifold Commutators -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ManifoldCommutators.Constructions

noncomputable section

/-! Actual global cutoff commutators and their order-zero chart coefficients. -/

open scoped _root_.Manifold ContDiff BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveDCommutator (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) :=
  DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.comp (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf) -
    (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf).comp DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

def projectiveDeltaCommutator (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  (AdjointAlgebra.Constructions.projectiveCodifferential V n).comp (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf) -
    (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf).comp (AdjointAlgebra.Constructions.projectiveCodifferential V n)

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveCodifferential_operator_coefficients (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val z =
      SupportedOperator.Constructions.localFirstOrderValue (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n)
        (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val) z := by
  rw [AdjointLocality.Constructions.projectiveCodifferential_coefficients V n e he a z hz,
    LocalCoefficientOperators.Constructions.projectiveLocalAdjointCoefficients_operator_formula V e n he _
      (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) a) z hz]
  rfl

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem projectiveDCommutator_coefficients (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (projectiveDCommutator V n f hf a).val z =
      CutoffCommutator.Constructions.firstOrderCutoffCoefficient (fun i _ => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i)
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y)) z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z) := by
  have hsub := congrFun ((CoefficientLinearity.Constructions.euclideanChartCoefficientLinear V e (n + 1)).map_sub
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a)).val
    (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).val) z
  change EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (projectiveDCommutator V n f hf a).val z =
    EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a)).val z -
      EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).val z at hsub
  rw [hsub, EuclideanForms.Constructions.euclideanChartCoefficients_d V e he n _ z hz,
    RealMultiplier.Constructions.projectiveRealMultiplier_coefficients, EuclideanForms.Constructions.euclideanChartCoefficients_d V e he n a z hz]
  have hmul : EuclideanForms.Constructions.euclideanChartCoefficients V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a).val =
      fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y) • EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val y :=
    funext (RealMultiplier.Constructions.projectiveRealMultiplier_coefficients V e n f hf a)
  rw [hmul]
  have hfz := ((RealMultiplier.Constructions.projectiveRealFunction_chart_smooth V e he f hf).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have haz := ((EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he n a).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hp := CutoffCommutator.Constructions.localFirstOrderValue_real_smul (fun i _ => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i)
    (fun _ => 0) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y)) (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val) z hfz haz
  simp only [SupportedOperator.Constructions.localFirstOrderValue, zero_apply, add_zero] at hp
  unfold LocalAdjoint.Constructions.firstOrderCoordinateOperator
  rw [hp, add_sub_cancel_left]

theorem projectiveDeltaCommutator_coefficients (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (projectiveDeltaCommutator V n f hf a).val z =
      CutoffCommutator.Constructions.firstOrderCutoffCoefficient (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n)
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y)) z (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val z) := by
  have hsub := congrFun ((CoefficientLinearity.Constructions.euclideanChartCoefficientLinear V e n).map_sub
    (AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a)).val
    (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a)).val) z
  change EuclideanForms.Constructions.euclideanChartCoefficients V e n (projectiveDeltaCommutator V n f hf a).val z =
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a)).val z -
      EuclideanForms.Constructions.euclideanChartCoefficients V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a)).val z at hsub
  rw [hsub, projectiveCodifferential_operator_coefficients V e he n _ z hz,
    RealMultiplier.Constructions.projectiveRealMultiplier_coefficients V e n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a) z,
    projectiveCodifferential_operator_coefficients V e he n a z hz]
  have hmul : EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a).val =
      fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y) • EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val y :=
    funext (RealMultiplier.Constructions.projectiveRealMultiplier_coefficients V e (n + 1) f hf a)
  rw [hmul]
  have hfz := ((RealMultiplier.Constructions.projectiveRealFunction_chart_smooth V e he f hf).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have haz := ((EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) a).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hp := CutoffCommutator.Constructions.localFirstOrderValue_real_smul (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n)
    (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun y => f (MeasureVolume.Constructions.chartCoordinateInverse V e y)) (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val) z hfz haz
  exact sub_eq_iff_eq_add.mpr (hp.trans (add_comm _ _))

end

end OAI.Analysis.HodgeTheory.Decomposition.ManifoldCommutators.Constructions
