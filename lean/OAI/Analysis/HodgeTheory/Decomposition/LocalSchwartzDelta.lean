import OAI.Analysis.HodgeTheory.Decomposition.SupportedOperator
import OAI.Analysis.HodgeTheory.Decomposition.FrozenFourier

/-! # Local Schwartz Delta -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalSchwartzDelta.Constructions

noncomputable section

/-! The actual chart codifferential on smooth compactly supported coefficient
forms, bundled as a Schwartz function. -/

open scoped SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def projectiveLocalDeltaSchwartz
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (ha : HasCompactSupport a) (hs : tsupport a ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  (SupportedOperator.Constructions.localFirstOrderValue_compactSupport (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n)
    (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) a ha).toSchwartzMap
      (SupportedOperator.Constructions.localFirstOrderValue_smooth _ _ _ a (a.smooth ⊤) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hs
        (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he)
        (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient_smooth V e n he))

theorem projectiveLocalDeltaSchwartz_apply
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (ha : HasCompactSupport a) (hs : tsupport a ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveLocalDeltaSchwartz V e n he a ha hs x =
      (∑ i, LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x
        (fderiv ℝ (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) x (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i))) +
        LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n x (a x) := rfl

theorem projectiveLocalDeltaSchwartz_tsupport
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (ha : HasCompactSupport a) (hs : tsupport a ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    tsupport (projectiveLocalDeltaSchwartz V e n he a ha hs) ⊆ tsupport a :=
  SupportedOperator.Constructions.localFirstOrderValue_tsupport _ _ _ _

theorem projectiveLocalDeltaSchwartz_eq_coefficients
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (ha : HasCompactSupport a) (hs : tsupport a ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    projectiveLocalDeltaSchwartz V e n he a ha hs x = AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n a x :=
  (LocalCoefficientOperators.Constructions.projectiveLocalAdjointCoefficients_operator_formula V e n he a (a.smooth ⊤).contDiffOn x hx).symm

theorem projectiveFrozenDelta_apply
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x =
      ∑ i, LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z
        (fderiv ℝ (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) x (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)) := by
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let S := fun i => PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz (b.coord i).toContinuousLinearMap
  change -(FourierOperator.Constructions.schwartzFirstOrder b S a x) = _
  rw [FourierOperator.Constructions.schwartzFirstOrder_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol_apply]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalSchwartzDelta.Constructions
