import OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients

/-! # Euclidean Forms -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions

noncomputable section

/-! The metric and exterior derivative of actual manifold forms in the same
Euclidean coordinates used by the Fourier, Sobolev, and adjoint constructions. -/

open scoped ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

def euclideanChartForm (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n :=
  (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).compContinuousLinearMap
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ)

def euclideanChartCoefficients (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (euclideanChartForm V e n a z)

theorem euclideanChartCoefficients_eq_analytic
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    euclideanChartCoefficients V e n a z =
      SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  apply PiLp.ext
  intro s
  rw [euclideanChartCoefficients, SymbolDifferential.Constructions.exteriorCoordinateEquiv_apply, SymbolDifferential.Constructions.exteriorCoordinateEquiv_apply]
  rfl

include he

theorem euclideanChartForm_smooth (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ContDiffOn ℝ ∞ (euclideanChartForm V e n a.val) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have ha : ContDiffOn ℝ ∞ (a.val.inChart e) e.target := by
    simpa only [DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using a.smooth e he
  have hcomp := ha.comp ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)
  exact DifferentialForms.Manifold.Alternatization.contDiffOn_alternating_compContinuousLinearMap hcomp contDiffOn_const

theorem euclideanChartCoefficients_smooth (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ContDiffOn ℝ ∞ (euclideanChartCoefficients V e n a.val) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  ((SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).contDiff.restrict_scalars ℝ).comp_contDiffOn
    (euclideanChartForm_smooth V e he n a)

theorem euclideanChartForm_d (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    euclideanChartForm V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val z =
      extDeriv (euclideanChartForm V e n a.val) z := by
  have ha : ContDiffOn ℝ ∞ (a.val.inChart e) e.target := by
    simpa only [DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, Set.preimage_univ, Set.inter_univ] using a.smooth e he
  have hA := (ha.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hL : ContDiff ℝ ∞ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ
  have hder (w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : fderiv ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) w =
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ :=
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.fderiv
  have h := extDeriv_pullback (f := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) (x := z)
    hA hL.contDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  simp only [hder] at h
  change ((DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).compContinuousLinearMap _ = _
  rw [DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart a e he hz]
  exact h.symm

/-- Both the genuine exterior derivative and its explicit fixed-symbol operator have identical coefficients. -/
theorem euclideanChartCoefficients_d (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    euclideanChartCoefficients V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val z =
      LocalAdjoint.Constructions.firstOrderCoordinateOperator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (euclideanChartCoefficients V e n a.val) z := by
  unfold euclideanChartCoefficients
  rw [euclideanChartForm_d V e he n a z hz]
  exact SymbolDifferential.Constructions.exteriorDerivative_in_coordinates (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (euclideanChartForm V e n a.val) z
    (((euclideanChartForm_smooth V e he n a).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp))

/-- The weighted coordinate inner product is the genuine manifold form metric times its volume density. -/
theorem euclideanChartCoefficients_weighted_inner
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (euclideanChartCoefficients V e n a z))
      (euclideanChartCoefficients V e n b z) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b (MeasureVolume.Constructions.chartCoordinateInverse V e z)).re := by
  rw [euclideanChartCoefficients_eq_analytic, euclideanChartCoefficients_eq_analytic]
  simp only [AdjointCoefficients.Constructions.projectiveWeightedFormOperator, smul_apply, real_inner_smul_left]
  rw [CoordinateMetric.Constructions.projectiveCoordinateMetric_inner V e he (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz]
  have hp := ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
    (e.map_target hz) n a b
  have hp' : ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b (MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz n
        (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (b.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
    simpa only [e.right_inv hz, MeasureVolume.Constructions.chartCoordinateInverse] using hp
  rw [hp']

end

end OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions
