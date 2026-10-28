import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection

/-! # Closed One Chart Derivatives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneChartDerivatives.CM.Construction

noncomputable section

section

/-! The actual smooth type projections have the prescribed holomorphic
and antiholomorphic covector coefficients in every native chart. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem oneFormHolomorphicPart_inChart_apply (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (v : E) :
    (OneFormProjection.CM.Construction.oneFormHolomorphicPart a).val.inChart e y (fun _ => v) =
      ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (a.val.inChart e y)) v := by
  have hsub (α β : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1) : (α - β).inChart e = α.inChart e - β.inChart e := by
    funext z
    ext w
    rfl
  change (((1 / 2 : ℂ) • (a.val - Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a.val)).inChart e y) (fun _ => v) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, hsub, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart _ _ e he hy,
    inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]
  rfl

theorem oneFormAntiholomorphicPart_inChart_apply (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (v : E) :
    (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a).val.inChart e y (fun _ => v) =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (a.val.inChart e y)) v := by
  change (((1 / 2 : ℂ) • (a.val + Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a.val)).inChart e y) (fun _ => v) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.add_apply, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart _ _ e he hy,
    inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]
  rfl

theorem antiholomorphicDirectionalDerivative_comp_complexLinear {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    (L : E →L[ℂ] F) (f : F → ℂ) {x : E} (hf : DifferentiableAt ℝ f (L x)) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => f (L y)) x u =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative f (L x) (L u) := by
  have hd := hf.hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt
  change HasFDerivAt (fun y => f (L y)) ((fderiv ℝ f (L x)).comp (L.restrictScalars ℝ)) x at hd
  simp only [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, hd.fderiv, ContinuousLinearMap.comp_apply]
  change (1 / 2 : ℂ) * (fderiv ℝ f (L x) (L u) + Complex.I *
    fderiv ℝ f (L x) (L (Complex.I • u))) = _
  rw [map_smul]

end

/-! Closed global one-forms satisfy the actual mixed type-coefficient
derivative identity in every Euclidean projective chart. -/

open Filter
open scoped _root_.Topology

theorem variety_closed_oneForm_mixed_derivatives (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (j k : Fin V.complexDimension) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
      (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) k) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) =
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) j) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) := by
  let f := a.val.inChart e
  let H := fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)
  let A := fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM V.analyticModel ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y))
    (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)
  have hzy : EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z ∈ e.target := hz
  have hf := (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart a.property e he hzy).differentiableAt (by simp)
  have hclosed : extDeriv f (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) = 0 := by
    rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart a e he hzy, ha]
    rfl
  have hv (u : V.analyticModel) := hf.continuousAlternatingMap_apply_const (fun _ => u)
  have hH : DifferentiableAt ℝ H (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) :=
    ((hv (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)).sub
      ((hv (Complex.I • HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hA : DifferentiableAt ℝ A (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) :=
    ((hv (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)).add
      ((hv (Complex.I • HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have heqH : HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) k =ᶠ[𝓝 z]
      (fun w => H (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
    exact oneFormHolomorphicPart_inChart_apply a e he hw (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)
  have heqA : HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) j =ᶠ[𝓝 z]
      (fun w => A (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
    exact oneFormAntiholomorphicPart_inChart_apply a e he hw (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)
  calc
    _ = AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative H (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
        (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j) :=
      (AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr heqH _).trans
        (antiholomorphicDirectionalDerivative_comp_complexLinear
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap H hH _)
    _ = MetricDerivative.CM.Construction.holomorphicDirectionalDerivative A (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
        (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k) := ClosedOneMixedDerivatives.CM.Construction.closed_oneForm_mixed_derivatives f hf hclosed _ _
    _ = _ := ((MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr heqA _).trans
      (MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_comp_complexLinear
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap A hA _)).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneChartDerivatives.CM.Construction
