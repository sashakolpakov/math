import OAI.Analysis.HodgeTheory.Decomposition.ChartTestDifferentials
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy

/-! # Chart Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartEnergy.Constructions

noncomputable section

/-! The energy of actual chart-lifted manifold forms equals the derived
vector coefficient energy, including both lower-order terms. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem projectiveFrozenD_tsupport
    (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    tsupport (FrozenFourier.Constructions.projectiveFrozenD V n f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  apply hx
  rw [FrozenFourier.Constructions.projectiveFrozenD, FourierOperator.Constructions.schwartzFirstOrder_apply]
  simp only [fderiv_of_notMem_tsupport ℝ h, zero_apply, map_zero, Finset.sum_const_zero]

include he in
theorem projective_weighted_schwartz_pair_integrable
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hg : HasCompactSupport g) (hs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Integrable (fun x => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n x (f x)) (g x)) volume :=
  LocalAdjointForm.Constructions.smooth_inner_test_integrable volume _ g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).clm_apply (f.smooth ⊤).contDiffOn)
    (g.smooth ⊤) hg hs

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

include he in
theorem projective_supported_coordinate_pair_both
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (hb : ∀ x, x ∉ e.source → b x = 0) :
    (Form.Constructions.projectiveL2Pair V n a b).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z)) (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b.val z) := by
  rw [ChartTestDifferentials.Constructions.projective_supported_coordinate_pair V e he n a b hb]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val hz]
  · rw [show SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b.val z = 0 from Set.indicator_of_notMem hz _,
      inner_zero_right, inner_zero_right]

theorem projectiveChartTestLift_pair_both
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V n (ChartTestForms.Constructions.projectiveChartTestLift V e he n f hf hfs)
      (ChartTestForms.Constructions.projectiveChartTestLift V e he n g hg hgs)).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (f z)) (g z) := by
  rw [projective_supported_coordinate_pair_both V e he n _ _ (fun x hx =>
    ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n g hg hgs x
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hgs h)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [ChartTestForms.Constructions.projectiveChartTestLift_coefficients, ChartTestForms.Constructions.projectiveChartTestLift_coefficients])

theorem projectiveChartTestLift_d_pair_both
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestForms.Constructions.projectiveChartTestLift V e he n f hf hfs))
      (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestForms.Constructions.projectiveChartTestLift V e he n g hg hgs))).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z (FrozenFourier.Constructions.projectiveFrozenD V n f z))
        (FrozenFourier.Constructions.projectiveFrozenD V n g z) := by
  rw [projective_supported_coordinate_pair_both V e he (n + 1) _ _ (fun x hx =>
    SupportedCoordinates.Constructions.manifold_d_zero_off_closed V n (ChartTestForms.Constructions.projectiveChartTestLift V e he n g hg hgs)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hgs).isClosed
      (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n g hg hgs)
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hgs h)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [ChartTestDifferentials.Constructions.projectiveChartTestLift_d_coefficients, ChartTestDifferentials.Constructions.projectiveChartTestLift_d_coefficients])

theorem projectiveChartTestLift_delta_pair_both
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) f hf hfs))
      (AdjointAlgebra.Constructions.projectiveCodifferential V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs))).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs z))
        (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he g hg hgs z) := by
  rw [projective_supported_coordinate_pair_both V e he n _ _ (fun x hx =>
    CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n (ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hgs).isClosed
      (ChartTestForms.Constructions.projectiveChartTestLift_zero V e he (n + 1) g hg hgs)
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hgs h)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [ChartTestDifferentials.Constructions.projectiveChartTestLift_delta_coefficients, ChartTestDifferentials.Constructions.projectiveChartTestLift_delta_coefficients])

theorem projectiveChartTestLift_hodge_energy
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    let a := ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) f hf hfs
    let b := ChartTestForms.Constructions.projectiveChartTestLift V e he (n + 1) g hg hgs
    let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
    (Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) +
      Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) (AdjointAlgebra.Constructions.projectiveCodifferential V n b)).re =
    ∫ x, inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x) := by
  dsimp only
  rw [Complex.add_re, projectiveChartTestLift_d_pair_both, projectiveChartTestLift_delta_pair_both]
  have hD := projectiveFrozenD_tsupport V (n + 1) g
  have hδ := LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz_tsupport V e n he g hg hgs
  rw [← integral_add
    (projective_weighted_schwartz_pair_integrable V e he (n + 1 + 1) _ _
      (hg.of_isClosed_subset (isClosed_tsupport _) hD) (hD.trans hgs))
    (projective_weighted_schwartz_pair_integrable V e he n _ _
      (hg.of_isClosed_subset (isClosed_tsupport _) hδ) (hδ.trans hgs))]
  exact integral_congr_ae (SchwartzEnergy.Constructions.projectiveHodge_schwartz_energy_expansion V e n he f g hf hfs hg hgs)

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartEnergy.Constructions
