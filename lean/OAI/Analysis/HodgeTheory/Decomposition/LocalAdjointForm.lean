import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv

/-! # Local Adjoint Form -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions

noncomputable section

section

/-! Integration by parts with coefficients smooth only on their actual chart
domain. Compact test support supplies the needed boundary condition. -/

open scoped ContDiff _root_.Topology BigOperators
open _root_.MeasureTheory

section Local

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem smooth_inner_test (w u : E → F) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ U) :
    ContDiff ℝ ∞ (fun x => inner ℝ (w x) (u x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (hw.contDiffAt (hU.mem_nhds hx)).inner ℝ hu.contDiffAt
  · have hz : u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    have heq : (fun y => inner ℝ (w y) (u y)) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      rw [hy, Pi.zero_apply, inner_zero_right]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem smoothOn_directional_derivative (w : E → F) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (v : E) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ w x v) U := by
  intro x hx
  exact (((hw.contDiffAt (hU.mem_nhds hx)).fderiv_right (by simp)).clm_apply
    contDiffAt_const).contDiffWithinAt

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem smooth_inner_test_integrable (w u : E → F) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) (hs : tsupport u ⊆ U) :
    Integrable (fun x => inner ℝ (w x) (u x)) μ :=
  (smooth_inner_test w u hU hw hu hs).continuous.integrable_of_hasCompactSupport
    (LocalAdjoint.Constructions.compactSupport_inner_right w u huc)

theorem integral_inner_directional_on (w u : E → F) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) (hs : tsupport u ⊆ U) (v : E) :
    (∫ x, inner ℝ (w x) (fderiv ℝ u x v) ∂μ) =
      -(∫ x, inner ℝ (fderiv ℝ w x v) (u x) ∂μ) := by
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    (smooth_inner_test_integrable μ _ u hU (smoothOn_directional_derivative w hU hw v) hu huc hs)
    (smooth_inner_test_integrable μ w _ hU hw (LocalAdjoint.Constructions.smooth_directional_derivative u hu v)
      (huc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs))
    (smooth_inner_test_integrable μ w u hU hw hu huc hs)
    (fun x hx => (hw.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt (by simp))
    (fun x _ => (hu.differentiable (by simp)).differentiableAt)

end Local

section Operator

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem firstOrderCoordinateOperator_integration_on (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (directions : ι → E) (symbol : ι → F →L[ℝ] G) (weight : E → G →L[ℝ] G)
    {U : Set E} (hU : IsOpen U) (hweight : ContDiffOn ℝ ∞ weight U)
    (u : E → F) (v : E → G) (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v U)
    (huc : HasCompactSupport u) (hs : tsupport u ⊆ U) :
    (∫ x, inner ℝ (weight x (v x)) (LocalAdjoint.Constructions.firstOrderCoordinateOperator directions symbol u x) ∂μ) =
      ∫ x, inner ℝ (LocalAdjoint.Constructions.formalAdjointNumerator directions symbol weight v x) (u x) ∂μ := by
  let w (i : ι) (x : E) : F := (symbol i).adjoint (weight x (v x))
  have hw (i : ι) : ContDiffOn ℝ ∞ (w i) U :=
    (symbol i).adjoint.contDiff.comp_contDiffOn (hweight.clm_apply hv)
  have hi (i : ι) : Integrable (fun x => inner ℝ (w i x) (fderiv ℝ u x (directions i))) μ :=
    smooth_inner_test_integrable μ _ _ hU (hw i) (LocalAdjoint.Constructions.smooth_directional_derivative u hu (directions i))
      (huc.fderiv_apply ℝ (directions i)) ((tsupport_fderiv_apply_subset ℝ (directions i)).trans hs)
  have hi' (i : ι) : Integrable (fun x => inner ℝ (fderiv ℝ (w i) x (directions i)) (u x)) μ :=
    smooth_inner_test_integrable μ _ _ hU (smoothOn_directional_derivative (w i) hU (hw i) (directions i)) hu huc hs
  calc
    (∫ x, inner ℝ (weight x (v x)) (LocalAdjoint.Constructions.firstOrderCoordinateOperator directions symbol u x) ∂μ) =
        ∫ x, ∑ i, inner ℝ (w i x) (fderiv ℝ u x (directions i)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [LocalAdjoint.Constructions.firstOrderCoordinateOperator, inner_sum, w, ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ i, ∫ x, inner ℝ (w i x) (fderiv ℝ u x (directions i)) ∂μ :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = ∑ i, -(∫ x, inner ℝ (fderiv ℝ (w i) x (directions i)) (u x) ∂μ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_inner_directional_on μ (w i) u hU (hw i) hu huc hs (directions i)
    _ = -(∫ x, ∑ i, inner ℝ (fderiv ℝ (w i) x (directions i)) (u x) ∂μ) := by
      rw [integral_finsetSum _ (fun i _ => hi' i), Finset.sum_neg_distrib]
    _ = ∫ x, inner ℝ (LocalAdjoint.Constructions.formalAdjointNumerator directions symbol weight v x) (u x) ∂μ := by
      simp only [LocalAdjoint.Constructions.formalAdjointNumerator, inner_neg_left, sum_inner, integral_neg, w]

end Operator

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

/-- The local adjoint is the unique solution of its positive metric equation. -/
theorem projectiveLocalAdjointCoefficients_weighted
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n v z) =
      LocalAdjoint.Constructions.formalAdjointNumerator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1)) v z :=
  (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_isInvertible V e he n z hz).self_apply_inverse _

/-- Integration by parts for the actual chart density and both actual degree metrics. -/
theorem projectiveLocalAdjointCoefficients_integration
    (u : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    (huc : HasCompactSupport u) (hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z (v z))
      (LocalAdjoint.Constructions.firstOrderCoordinateOperator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) u z)) =
    ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
      (AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n v z)) (u z) := by
  rw [firstOrderCoordinateOperator_integration_on volume _ _ _
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he (n + 1))
    u v hu hv huc hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · rw [projectiveLocalAdjointCoefficients_weighted V e he n v z hz]
  · have hzero : u z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    rw [hzero, inner_zero_right, inner_zero_right]

end

/-! The coordinate formal adjoint as an actual smooth tangent-covector field
on its chart source. -/

open scoped ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

def analyticFormOfEuclideanCoefficients
    (c : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (y : V.analyticModel) : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n :=
  (SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n).symm
    (c ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y))

def chartFormOfEuclideanCoefficients
    (c : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n :=
  DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart e (analyticFormOfEuclideanCoefficients V n c)

theorem analyticFormOfEuclideanCoefficients_smooth
    (c : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hc : ContDiffOn ℝ ∞ c (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _)) :
    ContDiffOn ℝ ∞ (analyticFormOfEuclideanCoefficients V n c) e.target := by
  apply ((SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n).symm.contDiff.restrict_scalars ℝ).comp_contDiffOn
  apply hc.comp ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.contDiff.restrict_scalars ℝ).contDiffOn
  intro y hy
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y) ∈ e.target
  rwa [ContinuousLinearEquiv.apply_symm_apply]

include he

theorem chartFormOfEuclideanCoefficients_smooth
    (c : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hc : ContDiffOn ℝ ∞ c (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _)) :
    DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (chartFormOfEuclideanCoefficients V e n c) e.source :=
  DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_smooth e he _ (analyticFormOfEuclideanCoefficients_smooth V e n c hc)

theorem chartFormOfEuclideanCoefficients_inverse
    (c : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (chartFormOfEuclideanCoefficients V e n c) z = c z := by
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic]
  unfold chartFormOfEuclideanCoefficients
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply e he _ hz]
  simp only [analyticFormOfEuclideanCoefficients, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The explicit local adjoint as actual covectors on manifold tangent spaces. -/
def projectiveChartAdjoint
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n :=
  chartFormOfEuclideanCoefficients V e n
    (AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val))

theorem projectiveChartAdjoint_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (projectiveChartAdjoint V e n a) e.source :=
  chartFormOfEuclideanCoefficients_smooth V e he n _
    (AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients_smooth V e he n _ (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) a))

theorem projectiveChartAdjoint_coefficients
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (projectiveChartAdjoint V e n a) z =
      AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n (EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val) z :=
  chartFormOfEuclideanCoefficients_inverse V e he n _ z hz

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions
