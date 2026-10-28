import OAI.Analysis.HodgeTheory.Decomposition.GradientCoefficient
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport
import OAI.Analysis.HodgeTheory.Decomposition.GradientGarding
import OAI.Analysis.HodgeTheory.Decomposition.LocalSchwartzDelta

/-! # Hodge Frozen Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.HodgeFrozenGradient.Constructions

noncomputable section

/-! The actual frozen Hodge principal coefficient satisfies an integrated
coercivity estimate on the whole genuine vector-valued H¹ space. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

omit e he z hz in
theorem projectiveFrozenD_normalizedGradient
    (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      GradientRows.Constructions.normalizedGradientRow (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1))
        (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x) = FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x := by
  filter_upwards [SchwartzGradientSupport.Constructions.normalizedGradientRow_schwartz (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun _ => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1)) f] with x hx
  rw [hx, FrozenFourier.Constructions.projectiveFrozenD, FourierOperator.Constructions.schwartzFirstOrder_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem projectiveFrozenDelta_normalizedGradient
    (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)
        (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x) = FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f x := by
  filter_upwards [SchwartzGradientSupport.Constructions.normalizedGradientRow_schwartz (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun _ i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) f] with x hx
  rw [hx, LocalSchwartzDelta.Constructions.projectiveFrozenDelta_apply]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem projectiveFrozenGradient_energy
    (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :
    let g := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    (∫ x, inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z (g x)) (g x)) =
      (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x))
        (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x)).re) +
      (∫ x, (inner ℂ (PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f x))
        (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f x)).re) := by
  dsimp only
  have hD : Integrable (fun x => (inner ℂ
      (PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x))
      (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x)).re) volume :=
    Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable
      (SchwartzMap.postcompCLM (PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z) (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f))
      (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f))
  have hδ : Integrable (fun x => (inner ℂ
      (PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f x))
      (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f x)).re) volume :=
    Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable
      (SchwartzMap.postcompCLM (PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z) (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f))
      (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz f))
  rw [← integral_add hD hδ]
  apply integral_congr_ae
  filter_upwards [projectiveFrozenD_normalizedGradient V n f,
    projectiveFrozenDelta_normalizedGradient V e n he z hz f] with x hx hy
  rw [GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient_pair, hx, hy,
    CoordinateMetric.Constructions.euclidean_real_inner_eq_re, CoordinateMetric.Constructions.euclidean_real_inner_eq_re]
  rfl

include he hz in
theorem projectiveFrozenGradient_coercive :
    ∃ a : ℝ, 0 < a ∧
      ∀ u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u‖ ^ 2 ≤
          ∫ x, inner ℝ
            (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z
              (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u x))
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u x) := by
  obtain ⟨a, ha, hbound⟩ := FrozenEstimate.Constructions.projectiveFrozen_firstOrder_estimate V e n he z hz
  have hκ : ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact norm_ne_zero_iff.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hs (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)‖ ^ 2 ≤
      ∫ x, inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z
        (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x) := by
    have hm := SchwartzGradientSupport.Constructions.vectorSobolevGradient_schwartz_energy
      (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) f
    rw [GradientEnergy.Constructions.schwartz_gradient_energy] at hm
    have hm' := mul_left_cancel₀ hκ hm
    rw [hm', projectiveFrozenGradient_energy V e n he z hz f]
    exact hbound f
  refine ⟨a, ha, fun u => ?_⟩
  have h := GradientGarding.Constructions.gradient_garding_of_schwartz (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun _ => GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z) aestronglyMeasurable_const
    (Filter.Eventually.of_forall (fun _ => le_rfl : ∀ x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ‖GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z‖ ≤ ‖GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z‖))
    (a := a) (c := 0) (fun f => by simpa only [zero_mul, add_zero] using hs f) u
  simpa only [zero_mul, add_zero] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.HodgeFrozenGradient.Constructions
