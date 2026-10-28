import OAI.Analysis.HodgeTheory.Decomposition.ChartTestForms
import OAI.Analysis.HodgeTheory.Decomposition.SupportedSchwartz
import OAI.Analysis.HodgeTheory.Decomposition.Coordinate

/-! # Chart Test Differentials -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartTestDifferentials.Constructions

noncomputable section

section

/-! Both genuine manifold Hodge differentials of a lifted chart test form
have exactly the prescribed Euclidean differential coefficients. -/

open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem projectiveChartTestLift_schwartz
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    SupportedSchwartz.Constructions.supportedCoordinatesSchwartz V e he n
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
      (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs) (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n c hc hs) = c := by
  apply DFunLike.ext
  intro z
  exact ChartTestForms.Constructions.projectiveChartTestLift_coefficients V e he n c hc hs z

theorem projectiveChartTestLift_d_coefficients
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1)
      (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs)).val z = FrozenFourier.Constructions.projectiveFrozenD V n c z := by
  rw [← SupportedSchwartz.Constructions.supportedCoordinatesSchwartz_d V e he n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
    (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs) (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n c hc hs) z,
    projectiveChartTestLift_schwartz]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveChartTestLift_delta_coefficients
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
      (AdjointAlgebra.Constructions.projectiveCodifferential V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs)).val z =
      LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he c hc hs z := by
  have h := SupportedSchwartz.Constructions.supportedCoordinatesSchwartz_delta V e he n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
    (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs) (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he (n + 1) c hc hs) z
  dsimp only at h
  change SupportedOperator.Constructions.localFirstOrderValue (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i)
    (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (SupportedSchwartz.Constructions.supportedCoordinatesSchwartz V e he (n + 1)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
      (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs)
      (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he (n + 1) c hc hs)) z = _ at h
  rw [projectiveChartTestLift_schwartz] at h
  exact h.symm

end

/-! The actual manifold L² pairing with a chart test form is its genuine
weighted Euclidean coefficient pairing. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he in
theorem projective_supported_coordinate_pair
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (hb : ∀ x, x ∉ e.source → b x = 0) :
    (Form.Constructions.projectiveL2Pair V n a b).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b.val z) := by
  have hchart := ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val x).re)
    (Complex.continuous_re.comp (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V n a b)).aestronglyMeasurable
    (fun x hx => by rw [LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n a.val b.val x (hb x hx)]; rfl)
  change RCLike.re (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [← integral_re (Form.Constructions.projectiveFormPointPair_integrable V n a b)]
  change (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val b.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [hchart]
  calc
    _ = ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z))
          (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b.val z) := by
      apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul, SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n b.val hz,
        EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he n a.val b.val z hz]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [show SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b.val z = 0 from Set.indicator_of_notMem hz _,
        inner_zero_right])

theorem projectiveChartTestLift_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V n a (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs)).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) (c z) := by
  rw [projective_supported_coordinate_pair V e he n a _ (fun x hx =>
    ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n c hc hs x
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs h)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => congrArg
    (fun w => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) w)
    (ChartTestForms.Constructions.projectiveChartTestLift_coefficients V e he n c hc hs z))

theorem projectiveChartTestLift_d_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V (n + 1) a (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs))).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z
        (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val z)) (FrozenFourier.Constructions.projectiveFrozenD V n c z) := by
  have hzero : ∀ x, x ∉ e.source → DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs) x = 0 := by
    intro x hx
    exact SupportedCoordinates.Constructions.manifold_d_zero_off_closed V n (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs).isClosed
      (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n c hc hs)
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs h))
  rw [projective_supported_coordinate_pair V e he (n + 1) a _ hzero]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => congrArg
    (fun w => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z
      (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val z)) w)
    (projectiveChartTestLift_d_coefficients V e he n c hc hs z))

theorem projectiveChartTestLift_delta_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V n a (AdjointAlgebra.Constructions.projectiveCodifferential V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs))).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he c hc hs z) := by
  have hzero : ∀ x, x ∉ e.source → AdjointAlgebra.Constructions.projectiveCodifferential V n
      (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs) x = 0 := by
    intro x hx
    exact CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) c hc hs)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hc hs).isClosed
      (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he (n + 1) c hc hs)
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs h))
  rw [projective_supported_coordinate_pair V e he n a _ hzero]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => congrArg
    (fun w => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) w)
    (projectiveChartTestLift_delta_coefficients V e he n c hc hs z))

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartTestDifferentials.Constructions
