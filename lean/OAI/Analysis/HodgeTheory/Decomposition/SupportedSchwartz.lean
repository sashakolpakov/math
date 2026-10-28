import OAI.Analysis.HodgeTheory.Decomposition.LocalSchwartzDelta
import OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport

/-! # Supported Schwartz -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SupportedSchwartz.Constructions

noncomputable section

/-! Compactly supported genuine manifold forms have Schwartz chart
coefficients, and both actual Hodge differentials agree with their coordinate operators. -/

open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)

def supportedCoordinatesSchwartz
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0) :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n a.val hK hKe ha).toSchwartzMap
    (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n a hK hKe ha)

theorem supportedCoordinatesSchwartz_coe
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0) :
    (supportedCoordinatesSchwartz V e he n hK hKe a ha : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val := rfl

theorem supportedCoordinatesSchwartz_d
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (ha : ∀ x, x ∉ K → a x = 0)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    FrozenFourier.Constructions.projectiveFrozenD V n (supportedCoordinatesSchwartz V e he n hK hKe a ha) x =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x := by
  let u := supportedCoordinatesSchwartz V e he n hK hKe a ha
  by_cases hx : x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val hx,
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients_d V e he n a x hx]
    change FourierOperator.Constructions.schwartzFirstOrder _ _ u x = _
    rw [FourierOperator.Constructions.schwartzFirstOrder_apply]
    rfl
  · have hxt : x ∉ tsupport u := fun h => hx
      (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e n a.val hK hKe ha h)
    have hz := fderiv_of_notMem_tsupport ℝ hxt
    change FourierOperator.Constructions.schwartzFirstOrder _ _ u x = _
    rw [FourierOperator.Constructions.schwartzFirstOrder_apply]
    simp only [hz, zero_apply, map_zero, Finset.sum_const_zero]
    exact (Set.indicator_of_notMem hx _).symm

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem supportedCoordinatesSchwartz_delta
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) (ha : ∀ x, x ∉ K → a x = 0)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let u := supportedCoordinatesSchwartz V e he (n + 1) hK hKe a ha
    let hc : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e (n + 1) a.val hK hKe ha
    let hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e (n + 1) a.val hK hKe ha
    LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he u hc hs x =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val x := by
  dsimp only
  let u := supportedCoordinatesSchwartz V e he (n + 1) hK hKe a ha
  have hc : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e (n + 1) a.val hK hKe ha
  have hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e (n + 1) a.val hK hKe ha
  change LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he u hc hs x = _
  by_cases hx : x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · rw [LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz_eq_coefficients V e n he u hc hs x hx,
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val hx,
      AdjointLocality.Constructions.projectiveCodifferential_coefficients V n e he a x hx,
      LocalCoefficientOperators.Constructions.projectiveLocalAdjointCoefficients_operator_formula V e n he u (u.smooth ⊤).contDiffOn x hx,
      LocalCoefficientOperators.Constructions.projectiveLocalAdjointCoefficients_operator_formula V e n he _
        (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) a) x hx]
    have heq := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eventuallyEq V e (n + 1) a.val hx
    change (∑ i, LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x
      (fderiv ℝ (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) a.val) x
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i))) + _ = _
    rw [heq.fderiv_eq, show u x = EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val x from heq.eq_of_nhds]
  · have hxt : x ∉ tsupport (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he u hc hs) :=
      fun h => hx (hs (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz_tsupport V e n he u hc hs h))
    rw [image_eq_zero_of_notMem_tsupport hxt]
    exact (Set.indicator_of_notMem hx _).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.SupportedSchwartz.Constructions
