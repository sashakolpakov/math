import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormSupportedPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneCodifferentialParts

/-! # Two Form Energy -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy.CM.Construction

noncomputable section

/-! The exact projective two-form energy proves that both type
components of a closed, coclosed one-form are closed. -/

open _root_.MeasureTheory
open scoped ContDiff _root_.Manifold

theorem projective_closed_trace_zero_supported_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (ht : ∀ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, HolomorphicExteriorTrace.CM.Construction.varietyTwoFormTrace V e a z = 0)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hs : ∀ x, x ∉ K → b x = 0) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) = 0 := by
  let g := HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b
  have hg (j : Fin V.complexDimension) : ContDiff ℝ ∞ (g j) :=
    HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_smooth V e he b j hK hKe hs
  have hgc (j : Fin V.complexDimension) : HasCompactSupport (g j) :=
    HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_compact V e b j hK hKe hs
  have hgs (j : Fin V.complexDimension) : tsupport (g j) ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_tsupport_domain V e b j hK hKe hs
  have hw (j d : Fin V.complexDimension) := AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux_smooth V e he a j d
  have hint (j : Fin V.complexDimension) : Integrable
      (fun z => ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
        AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) volume :=
    integrable_finsetSum _ (fun d _ => AntiholomorphicIntegration.CM.Construction.antiholomorphic_test_product_integrable volume _ _
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (hw j d) (hg j) (hgc j) (hgs j) _)
  rw [TwoFormSupportedPair.CM.Construction.projectiveL2Pair_type11_supported_derivative V e he a ha b hb hK hKe hs,
    integral_finsetSum _ (fun j _ => hint j)]
  have hz (j : Fin V.complexDimension) :
      (∫ z, ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
        AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0 :=
    AntiholomorphicIntegration.CM.Construction.integral_divergence_free_antiholomorphic_flux volume _ _ (g j) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      (hw j) (hg j) (hgc j) (hgs j)
      (fun _ h => AntiholomorphicIntegration.CM.Construction.variety_closed_trace_zero_two_flux_divergence V e he a ha hc ht h j)
  change 4 * ∑ j, (∫ z, ∑ d, AntiholomorphicIntegration.CM.Construction.varietyMixedTwoAdjointFlux V e a j d z *
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0
  simp only [hz, Finset.sum_const_zero, mul_zero]

theorem type10_smulByFunction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a).val := by
  intro e he y hy
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a.val).inChart e y)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule V.analyticModel 1 0).smul_mem _ (ha e he y hy)

theorem projective_closed_trace_zero_type10_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (ht : ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel),
      e ∈ atlas V.analyticModel V.analyticSpace →
        ∀ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, HolomorphicExteriorTrace.CM.Construction.varietyTwoFormTrace V e a z = 0)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) = 0 := by
  let localB := fun i => Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition V i)
    (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition_smooth V i) b
  have hsum : (∑ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (localB i)) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b := by
    rw [← map_sum, Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projective_partition_forms_sum]
  rw [← hsum, Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveL2Pair_sum_right]
  apply Finset.sum_eq_zero
  intro i _
  apply projective_closed_trace_zero_supported_pair V (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveCoverChart V i)
    (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i) a ha hc
    (ht _ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i)) (localB i)
    (type10_smulByFunction V _ _ b hb)
    (K := tsupport (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition V i)) (isClosed_tsupport _).isCompact
    (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition_support V i)
  intro x hx
  change Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition V i x • b x = 0
  rw [image_eq_zero_of_notMem_tsupport hx]
  exact zero_smul ℂ (b x)

theorem coclosed_type10_mixed_derivative_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (hd : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val)
    (hc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a = 0) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 := by
  apply Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair_definite V 2
  apply projective_closed_trace_zero_type10_pair V (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hd
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared a) _ a ha
  intro e he z hz
  exact HolomorphicExteriorTrace.CM.Construction.variety_coclosed_type10_exterior_trace_zero V e he a ha hc hz

theorem closed_coclosed_oneForm_parts_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) (hc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) = 0 ∧
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) = 0 := by
  have hh := coclosed_type10_mixed_derivative_zero V (OneFormProjection.CM.Construction.oneFormHolomorphicPart a)
    (OneFormProjection.CM.Construction.oneFormHolomorphicPart_hasBidegree a)
    (OneFormProjection.CM.Construction.oneFormHolomorphicPart_derivative_hasBidegree ⟨a, ha⟩)
    (ClosedOneCodifferentialParts.CM.Construction.closed_coclosed_oneForm_parts_coclosed V a ha hc).1
  exact ⟨hh, OneFormProjection.CM.Construction.oneForm_antiholomorphicPart_closed ⟨a, ha⟩ hh⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy.CM.Construction
