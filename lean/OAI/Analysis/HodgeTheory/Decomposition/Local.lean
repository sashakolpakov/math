import OAI.Analysis.HodgeTheory.Decomposition.LocalFlux
import OAI.Analysis.HodgeTheory.Decomposition.VectorTestDensity

/-! # Local -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Local.Constructions

noncomputable section

/-! The actual lower-order Hodge coefficients satisfy the hypotheses of
the proved local H² theorem once the local weak energy equation is given. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projective_local_hodge_h2
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    {L : NNReal} (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hgard : ∀ y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ∀ v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v‖ ^ 2 ≤
          ∫ x, inner ℝ (A (x + y)
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
    (U : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : ∀ q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
        SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
      HasCompactSupport q → tsupport q ⊆ U →
        LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A
          hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) u
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) = inner ℝ f (q.toLp 2 volume))
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgU : tsupport g ⊆ U) :
    MemSobolev 2 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  let b := stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let F := LocalFlux.Constructions.projectiveLocalHodgeForcing V e n he η hη hηc hηU u f
  let H := LocalFlux.Constructions.projectiveLocalHodgeFlux V e n he η hη hηc hηU u
  have hAm := hA.continuous.aestronglyMeasurable (μ := (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
  have hCm : ∀ᵐ x ∂volume, ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  have htest (q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
      (hqc : HasCompactSupport q) (hqU : tsupport q ⊆ U) :
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) b u x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) x)) =
        inner ℝ F (q.toLp 2 volume) + inner ℝ H
          (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)) := by
    have heq := LocalFlux.Constructions.projectiveLocalHodgeEnergy_to_flux V e n he η hη hηc hηU A hAm hCm u
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) f (by
        rw [VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz]
        exact hsol q hqc hqU)
    dsimp only at heq
    rw [VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz] at heq
    exact heq
  obtain ⟨w, hw⟩ := LocalFlux.Constructions.projectiveLocalHodgeFlux_has_H1_coordinate V e n he η hη hηc hηU u
  apply VectorLocalElliptic.Constructions.vector_local_elliptic_flux_h2 b A hA hC ha (c := 0) (by norm_num)
    (fun y v => by simpa only [pow_two, mul_assoc, zero_mul, add_zero] using hgard y v)
    g hgreal u F w
  intro v
  rw [hw]
  exact VectorTestDensity.Constructions.vector_local_flux_of_schwartz_tests b A hAm hCm U u F H htest g hgc hgU v

end

end OAI.Analysis.HodgeTheory.Decomposition.Local.Constructions
