import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneChartDerivatives
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicCodifferential

/-! # Closed One Codifferential Parts -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneCodifferentialParts.CM.Construction

noncomputable section

/-! For a closed one-form the two type components have equal actual
codifferentials. Consequently a coclosed closed one-form has coclosed
holomorphic and antiholomorphic components. -/

theorem variety_closed_oneForm_contractions (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    HolomorphicCodifferential.CM.Construction.varietyHolomorphicAdjointContraction V e (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) z =
      AntiholomorphicCodifferential.CM.Construction.varietyAntiholomorphicAdjointContraction V e (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) z := by
  rw [HolomorphicCodifferential.CM.Construction.varietyHolomorphicAdjointContraction, AntiholomorphicCodifferential.CM.Construction.varietyAntiholomorphicAdjointContraction]
  calc
    _ = ∑ j, ∑ k, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ k j *
        MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
          (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) j) z
          (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      exact ClosedOneChartDerivatives.CM.Construction.variety_closed_oneForm_mixed_derivatives V e he a ha hz j k
    _ = _ := Finset.sum_comm

theorem closed_oneForm_codifferential_parts (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) =
      Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  let z := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)
  have hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hx
  have h : ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a)) z =
      ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a)) z := by
    rw [HolomorphicCodifferential.CM.Construction.varietyHolomorphicCodifferential_formula V e he _ (OneFormProjection.CM.Construction.oneFormHolomorphicPart_hasBidegree a) hz,
      AntiholomorphicCodifferential.CM.Construction.varietyAntiholomorphicCodifferential_formula V e he _ (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart_hasBidegree a) hz,
      variety_closed_oneForm_contractions V e he a ha hz]
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv]
  have hpoint : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) = x := by
    dsimp only [z]
    rw [ContinuousLinearEquiv.apply_symm_apply, e.left_inv hx]
  change HolomorphicPrimitive.CM.Construction.zeroFormScalar (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a))
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) =
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a))
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) at h
  rw [hpoint] at h
  exact h

theorem closed_coclosed_oneForm_parts_coclosed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) (hδ : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a = 0) :
    Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) = 0 ∧
      Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) = 0 := by
  have heq := closed_oneForm_codifferential_parts V a ha
  have hsum := congrArg (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0) (OneFormProjection.CM.Construction.oneForm_parts_add a)
  rw [map_add, hδ, ← heq] at hsum
  have hz : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) = 0 := by
    have htwo : (2 : ℂ) • Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (OneFormProjection.CM.Construction.oneFormHolomorphicPart a) = 0 := by
      simpa only [two_smul] using hsum
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨hz, heq.symm.trans hz⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneCodifferentialParts.CM.Construction
