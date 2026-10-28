import OAI.Analysis.HodgeTheory.Decomposition.GradientRows
import OAI.Analysis.HodgeTheory.Decomposition.LocalCoefficientOperators

/-! # Gradient Coefficient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GradientCoefficient.Constructions

noncomputable section

section

/-! The actual smooth principal coefficient operator for the local Hodge
energy, acting on all directional form coefficients. -/

open scoped ContDiff BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

abbrev ProjectiveGradientValues :=
  PiLp 2 (fun _ : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V =>
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))

def projectiveHodgeGradientCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ProjectiveGradientValues V n →L[ℝ] ProjectiveGradientValues V n :=
  GradientRows.Constructions.weightedGradientGram (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1))
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) z) +
  GradientRows.Constructions.weightedGradientGram (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z)

theorem projectiveHodgeGradientCoefficient_pair (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (v w : ProjectiveGradientValues V n) :
    inner ℝ (projectiveHodgeGradientCoefficient V e n z v) w =
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) z
        (GradientRows.Constructions.normalizedGradientRow (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1)) v))
        (GradientRows.Constructions.normalizedGradientRow (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1)) w) +
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) v))
        (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) w) := by
  rw [projectiveHodgeGradientCoefficient, add_apply, inner_add_left]
  exact congrArg₂ (· + ·)
    (GradientRows.Constructions.weightedGradientGram_pair (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1))
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) z) v w)
    (GradientRows.Constructions.weightedGradientGram_pair (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z) v w)

theorem projectiveHodgeGradientCoefficient_smooth
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (projectiveHodgeGradientCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have hS (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) : ContDiffOn ℝ ∞
      (fun _ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1) i)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := contDiffOn_const
  have hD := GradientRows.Constructions.weightedGradientGram_smooth
    (S := fun _ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1))
    hS
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he (n + 1 + 1))
  have hδ := GradientRows.Constructions.weightedGradientGram_smooth
    (S := fun x i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x)
    (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he i)
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n)
  exact hD.add hδ

end

/-! Actual lower-order coefficients in the local Hodge weak equation.
The flux is a smooth coefficient times the form value, and the remaining
zeroth-order pairing factors through the actual codifferential value. -/

open scoped ContDiff BigOperators

theorem real_adjoint_smoothOn {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {U : Set E} {A : E → F →L[ℝ] G} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjoint) U :=
  (ContinuousLinearMap.adjoint : (F →L[ℝ] G) ≃ₗᵢ[ℝ] (G →L[ℝ] F)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hA

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def projectiveHodgeFluxCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) →L[ℝ] ProjectiveGradientValues V n :=
  (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)).adjoint.comp
    ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).comp (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z))

def projectiveHodgeValueCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) :=
  (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z).adjoint.comp (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z)

theorem projectiveHodgeFluxCoefficient_smooth
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (projectiveHodgeFluxCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have hrow := GradientRows.Constructions.normalizedGradientRow_smooth
    (S := fun z i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)
    (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he i)
  exact (real_adjoint_smoothOn hrow).clm_comp
    ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).clm_comp
      (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient_smooth V e n he))

theorem projectiveHodgeValueCoefficient_smooth
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (projectiveHodgeValueCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (real_adjoint_smoothOn (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient_smooth V e n he)).clm_comp
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n)

theorem projectiveHodge_energy_expansion (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (u v : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (p q : ProjectiveGradientValues V n) :
    let D := GradientRows.Constructions.normalizedGradientRow (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V (n + 1))
    let T := GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)
    let Z := LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z
    inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) z (D p)) (D q) +
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (T p + Z u)) (T q + Z v) =
      inner ℝ (projectiveHodgeGradientCoefficient V e n z p) q +
        inner ℝ (projectiveHodgeFluxCoefficient V e n z u) q +
        inner ℝ (projectiveHodgeValueCoefficient V e n z (T p + Z u)) v := by
  dsimp only
  rw [projectiveHodgeGradientCoefficient_pair]
  have hflux : inner ℝ (projectiveHodgeFluxCoefficient V e n z u) q =
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z u))
        (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) q) :=
    ContinuousLinearMap.adjoint_inner_left
      (GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z)) q
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z u))
  have hvalue (w : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
      inner ℝ (projectiveHodgeValueCoefficient V e n z w) v =
        inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z w) (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z v) :=
    ContinuousLinearMap.adjoint_inner_left (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n z) v
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z w)
  rw [hflux, hvalue, inner_add_right, map_add, inner_add_left]
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.GradientCoefficient.Constructions
