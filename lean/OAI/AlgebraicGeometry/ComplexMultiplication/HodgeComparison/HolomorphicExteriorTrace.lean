import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormChartCoefficients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedDerivative
import OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates

/-! # Holomorphic Exterior Trace -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction

noncomputable section

section

/-! The genuine codifferential of a (1,0) one-form is minus twice the
Hermitian trace of its genuine exterior derivative. -/

open scoped ContDiff _root_.Topology

theorem varietyOneFormComplexCoefficient_eq_euclidean (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (i : Fin V.complexDimension) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.val z
        (fun _ => EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) := rfl

theorem variety_type10_exterior_mixed_coefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j : Fin V.complexDimension) :
    TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) i j z =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a j) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) := by
  let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.val
  have hf : DifferentiableAt ℝ f z :=
    ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 1 a).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have ht : ∀ᶠ y in 𝓝 z, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 0 (f y) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    intro c v
    change a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)
      (fun l => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • v l)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 c * a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)
        (fun l => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (v l))
    simp only [map_smul]
    exact ha e he _ hy c _
  rw [TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient_eq_euclidean, Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_d V e he 1 a z hz,
    HolomorphicMixedDerivative.CM.Construction.mixedTwoCoefficient_extDeriv_type10 f hf ht]
  rfl

def varietyTwoFormTrace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  ∑ j, ∑ k, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ k j * TwoFormChartCoefficients.CM.Construction.varietyTwoFormMixedCoefficient V e a j k z

theorem variety_type10_codifferential_trace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) z =
      -2 * varietyTwoFormTrace V e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) z := by
  rw [HolomorphicCodifferential.CM.Construction.varietyHolomorphicCodifferential_formula V e he a ha hz]
  congr 1
  unfold HolomorphicCodifferential.CM.Construction.varietyHolomorphicAdjointContraction varietyTwoFormTrace
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (variety_type10_exterior_mixed_coefficient V e he a ha hz j k).symm

theorem variety_coclosed_type10_exterior_trace_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (hc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    varietyTwoFormTrace V e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) z = 0 := by
  have h := variety_type10_codifferential_trace V e he a ha hz
  rw [hc] at h
  change 0 = -2 * varietyTwoFormTrace V e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) z at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

end

/-! Complex coefficients of a genuinely supported smooth one-form
extend by zero to compactly supported smooth Euclidean test functions. -/

open Filter
open scoped ContDiff _root_.Topology

def supportedOneFormComplexCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _).indicator (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i)

theorem supportedOneFormComplexCoefficient_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    supportedOneFormComplexCoefficient V e a i z = HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i z :=
  Set.indicator_of_mem hz _

theorem supportedOneFormComplexCoefficient_eventuallyEq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    supportedOneFormComplexCoefficient V e a i =ᶠ[𝓝 z] HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i := by
  filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
  exact supportedOneFormComplexCoefficient_eq V e a i hy

theorem varietyOneFormComplexCoefficient_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) (ha : a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0) :
    HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i z = 0 := by
  have hchart : a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) = 0 := by
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    change (a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).compContinuousLinearMap _ = 0
    rw [ha]
    ext v
    rfl
  rw [HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient, hchart]
  rfl

theorem supportedOneFormComplexCoefficient_support (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {K : Set V.analyticSpace} (ha : ∀ x, x ∉ K → a x = 0) :
    Function.support (supportedOneFormComplexCoefficient V e a i) ⊆
      Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K := by
  intro z hz
  have hzU : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    by_contra hn
    exact hz (Set.indicator_of_notMem hn _)
  refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, ?_, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzU⟩
  by_contra hx
  apply hz
  rw [supportedOneFormComplexCoefficient_eq V e a i hzU]
  exact varietyOneFormComplexCoefficient_zero V e a i z (ha _ hx)

theorem supportedOneFormComplexCoefficient_tsupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    tsupport (supportedOneFormComplexCoefficient V e a i) ⊆ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' K :=
  closure_minimal (supportedOneFormComplexCoefficient_support V e a i ha)
    (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe).isClosed

theorem supportedOneFormComplexCoefficient_compact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    HasCompactSupport (supportedOneFormComplexCoefficient V e a i) :=
  (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe).of_isClosed_subset (isClosed_tsupport _)
    (supportedOneFormComplexCoefficient_tsupport V e a i hK hKe ha)

theorem supportedOneFormComplexCoefficient_tsupport_domain (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    tsupport (supportedOneFormComplexCoefficient V e a i) ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := supportedOneFormComplexCoefficient_tsupport V e a i hK hKe ha hz
  exact Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)

theorem supportedOneFormComplexCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (i : Fin V.complexDimension)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    ContDiff ℝ ∞ (supportedOneFormComplexCoefficient V e a i) := by
  apply Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.smooth_of_support_in_closed _
    (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe).isClosed (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
  · rintro z ⟨x, hx, rfl⟩
    exact Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  · exact supportedOneFormComplexCoefficient_support V e a i ha
  · exact (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient_smooth V e he a i).congr
      (fun z hz => supportedOneFormComplexCoefficient_eq V e a i hz)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction
