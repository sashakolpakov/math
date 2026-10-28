import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoSupportedPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy

/-! # Two Energy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoEnergy.Closedness

noncomputable section

/-! An exact (2,0) derivative of a (1,0) form vanishes on a projective variety. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy.CM.Construction _root_.MeasureTheory
open scoped ContDiff _root_.Manifold

theorem projective_closed_type20_supported_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hs : ∀ x, x ∉ K → b x = 0) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 a (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) = 0 := by
  let g := fun j z => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j z)
  have hg (j : Fin V.complexDimension) : ContDiff ℝ ∞ (g j) :=
    Complex.conjCLE.contDiff.comp (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_smooth V e he b j hK hKe hs)
  have hgc (j : Fin V.complexDimension) : HasCompactSupport (g j) := by
    change IsCompact (tsupport (fun z => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j z)))
    rw [TwoSupportedPair.Closedness.tsupport_conjugate]
    exact ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_compact V e b j hK hKe hs
  have hgs (j : Fin V.complexDimension) : tsupport (g j) ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change tsupport (fun z => star (ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient V e b j z)) ⊆ _
    rw [TwoSupportedPair.Closedness.tsupport_conjugate]
    exact ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction.supportedOneFormComplexCoefficient_tsupport_domain V e b j hK hKe hs
  have hw (j d : Fin V.complexDimension) := ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux_smooth V e he a j d
  have hint (j : Fin V.complexDimension) : Integrable
      (fun z => ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
        ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) volume :=
    integrable_finsetSum _ (fun d _ => ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.antiholomorphic_test_product_integrable volume _ _
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (hw j d) (hg j) (hgc j) (hgs j) _)
  have hz (j : Fin V.complexDimension) :
      (∫ z, ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
        ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0 :=
    ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.integral_divergence_free_antiholomorphic_flux volume _ _ (g j) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      (hw j) (hg j) (hgc j) (hgs j)
      (fun _ h => ProjectiveTwoFlux.Closedness.variety_closed_type20_flux_divergence V e he a ha hc h j)
  have hpair : Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 2 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) a = 0 := by
    rw [TwoSupportedPair.Closedness.projectiveL2Pair_type20_supported_derivative V e he a ha b hb hK hKe hs,
      integral_finsetSum _ (fun j _ => hint j)]
    change 4 * ∑ j, (∫ z, ∑ d, ProjectiveTwoFlux.Closedness.varietyHolomorphicTwoFlux V e a j d z *
      ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (g j) z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0
    simp only [hz, Finset.sum_const_zero, mul_zero]
  rw [← Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair_symm, hpair, star_zero]

theorem projective_closed_type20_type10_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
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
  apply projective_closed_type20_supported_pair V (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveCoverChart V i)
    (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i) a ha hc (localB i)
    (ComplexMultiplication.HodgeComparison.TwoFormEnergy.CM.Construction.type10_smulByFunction V _ _ b hb)
    (K := tsupport (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition V i)) (isClosed_tsupport _).isCompact
    (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition_support V i)
  intro x hx
  change Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveAdjointPartition V i x • b x = 0
  rw [image_eq_zero_of_notMem_tsupport hx]
  exact zero_smul ℂ (b x)

/-- Closedness is deduced from the actual positive metric pairing and d² = 0. -/
theorem projective_type10_with_type20_derivative_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (hd : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 := by
  apply Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair_definite V 2
  exact projective_closed_type20_type10_pair V (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hd
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared a) a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoEnergy.Closedness
