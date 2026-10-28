import OAI.Analysis.HodgeTheory.Decomposition.DerivativeComplexLinearity
import OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift
import OAI.Analysis.HodgeTheory.Decomposition.GradientCoefficient

/-! # Coefficient Hodge -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CoefficientHodge.Constructions

noncomputable section

section

/-! The actual local Hodge principal and lower-order coefficient operators
are complex-linear, including the coefficients obtained by differentiating
the metric and taking real Hilbert adjoints. -/

theorem normalizedGradientRow_complex_smul {F G ι : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [InnerProductSpace ℝ G] [IsScalarTower ℝ ℂ G]
    (S : ι → F →L[ℝ] G) (hS : ∀ i (c : ℂ) (u : F), S i (c • u) = c • S i u)
    (c : ℂ) (u : PiLp 2 (fun _ : ι => F)) : GradientRows.Constructions.normalizedGradientRow S (c • u) = c • GradientRows.Constructions.normalizedGradientRow S u := by
  rw [GradientRows.Constructions.normalizedGradientRow_apply, GradientRows.Constructions.normalizedGradientRow_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.smul_apply, smul_comm (2 * Real.pi * Complex.I : ℂ) c, hS]

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

omit e in
theorem projectiveEuclideanExteriorSymbol_complex_smul (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i (c • u) = c • AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i u :=
  ComplexMetric.Constructions.coordinateCovectorSymbol_complex_smul (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (((stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis.coord i).toContinuousLinearMap) u c

omit e in
theorem projectiveExteriorAdjoint_complex_smul (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i).adjoint (c • u) =
      c • (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i).adjoint u :=
  ComplexOperatorLift.Constructions.real_adjoint_complex_smul _ (projectiveEuclideanExteriorSymbol_complex_smul V n i) c u

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

include he hx in
theorem projectiveAdjointPrincipalCoefficient_complex_smul (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x (c • u) =
      c • LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x u := by
  simp only [LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient, neg_apply, ContinuousLinearMap.comp_apply]
  rw [ComplexMetric.Constructions.projectiveWeightedFormOperator_complex_smul, projectiveExteriorAdjoint_complex_smul,
    ComplexMetric.Constructions.projectiveWeightedFormOperator_inverse_complex_smul V e n he x hx, smul_neg]

include he hx in
theorem projectiveAdjointZeroCoefficient_complex_smul
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n x (c • u) = c • LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n x u := by
  simp only [LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient, neg_apply, ContinuousLinearMap.comp_apply, sum_apply]
  simp_rw [DerivativeComplexLinearity.Constructions.projectiveWeightedFormOperator_derivative_complex_smul V e he (n + 1) x hx,
    projectiveExteriorAdjoint_complex_smul]
  rw [← Finset.smul_sum, ComplexMetric.Constructions.projectiveWeightedFormOperator_inverse_complex_smul V e n he x hx, smul_neg]

include he hx in
theorem projectiveHodgeFluxCoefficient_complex_smul
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (c • u) = c • GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x u := by
  have hT := normalizedGradientRow_complex_smul
    (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x)
    (fun i => projectiveAdjointPrincipalCoefficient_complex_smul V e n he x hx i)
  simp only [GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient, ContinuousLinearMap.comp_apply]
  rw [projectiveAdjointZeroCoefficient_complex_smul V e n he x hx,
    ComplexMetric.Constructions.projectiveWeightedFormOperator_complex_smul, ComplexOperatorLift.Constructions.real_adjoint_complex_smul _ hT]

include he hx in
theorem projectiveHodgeValueCoefficient_complex_smul
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (c • u) = c • GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x u := by
  simp only [GradientCoefficient.Constructions.projectiveHodgeValueCoefficient, ContinuousLinearMap.comp_apply]
  rw [ComplexMetric.Constructions.projectiveWeightedFormOperator_complex_smul,
    ComplexOperatorLift.Constructions.real_adjoint_complex_smul _ (projectiveAdjointZeroCoefficient_complex_smul V e n he x hx)]

end

section

/-! The remaining Hodge value term splits into a coefficient times the
gradient and a coefficient times the value, with genuine smooth coefficients. -/

open scoped ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def projectiveHodgeValueGradientCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) :=
  (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n z).comp
    (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z))

def projectiveHodgeValueValueCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) :=
  (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n z).comp (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z)

theorem projectiveHodgeValue_expansion (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (p : GradientCoefficient.Constructions.ProjectiveGradientValues V n) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n z
      (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) p +
        LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z u) =
      projectiveHodgeValueGradientCoefficient V e n z p + projectiveHodgeValueValueCoefficient V e n z u :=
  map_add _ _ _

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he in
theorem projectiveHodgeValueGradientCoefficient_smooth :
    ContDiffOn ℝ ∞ (projectiveHodgeValueGradientCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient_smooth V e n he).clm_comp
    (GradientRows.Constructions.normalizedGradientRow_smooth (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he i))

include he in
theorem projectiveHodgeValueValueCoefficient_smooth :
    ContDiffOn ℝ ∞ (projectiveHodgeValueValueCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient_smooth V e n he).clm_comp
    (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient_smooth V e n he)

include he in
theorem projectiveHodgeValueGradientCoefficient_complex_smul
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (c : ℂ) (u : GradientCoefficient.Constructions.ProjectiveGradientValues V n) :
    projectiveHodgeValueGradientCoefficient V e n z (c • u) =
      c • projectiveHodgeValueGradientCoefficient V e n z u := by
  simp only [projectiveHodgeValueGradientCoefficient, ContinuousLinearMap.comp_apply]
  rw [normalizedGradientRow_complex_smul _
    (fun i => projectiveAdjointPrincipalCoefficient_complex_smul V e n he z hz i),
    projectiveHodgeValueCoefficient_complex_smul V e n he z hz]

include he in
theorem projectiveHodgeValueValueCoefficient_complex_smul
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    projectiveHodgeValueValueCoefficient V e n z (c • u) =
      c • projectiveHodgeValueValueCoefficient V e n z u := by
  simp only [projectiveHodgeValueValueCoefficient, ContinuousLinearMap.comp_apply]
  rw [projectiveAdjointZeroCoefficient_complex_smul V e n he z hz,
    projectiveHodgeValueCoefficient_complex_smul V e n he z hz]

end

/-! Pointwise collection of the actual lower-order Hodge energy terms. -/

theorem projectiveHodge_energy_lower_collect (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (p q : GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (u v : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (d : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hd : d = GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x) p +
      LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n x u) :
    inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x p) q +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x u) q +
      inner ℝ (projectiveHodgeValueGradientCoefficient V e n x p) v +
      inner ℝ (projectiveHodgeValueValueCoefficient V e n x u) v =
    inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x p) q +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x u) q +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x d) v := by
  rw [hd, projectiveHodgeValue_expansion, inner_add_left]
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.CoefficientHodge.Constructions
