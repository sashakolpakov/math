import OAI.AlgebraicGeometry.HodgeConjecture.CoefficientCups
import OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients
import OAI.AlgebraicGeometry.HodgeConjecture.Projection

/-! # Correspondence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Correspondence.CM.SurfaceConstruction

noncomputable section

/-! The four divisor correspondence on the genuine product S × X. -/

open _root_.CategoryTheory
open MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
  (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
  (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (f : ∀ i, S.toOver ⟶ (R i).abelianVariety.toOver)
  (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
  (τ : Fin 4 → E →ₐ[ℚ] ℂ)

def correspondenceDivisor (i : Fin 4) :
    E ⊗[ℚ] (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).rationalCohomology 2 :=
  Pairs.CM.SurfaceConstruction.normalizedOppositePair E (h i) (R i) (R i) (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (fst S.toOver X.toOver ≫ f i) (snd S.toOver X.toOver ≫ π i) (τ i)

def surfaceCorrespondence :
    E ⊗[ℚ] (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).rationalCohomology 8 :=
  CoefficientCups.CM.SurfaceConstruction.fourDivisorCup E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (correspondenceDivisor E H h R S X f π τ)

theorem surfaceCorrespondence_algebraic
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula) :
    surfaceCorrespondence E H h R S X f π τ ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) 4 := by
  apply CoefficientCups.CM.SurfaceConstruction.fourDivisorCup_algebraic E hThomClass hProjectionFormula
  intro i
  exact Pairs.CM.SurfaceConstruction.normalizedOppositePair_algebraic E hScalarDescent hDegreeTwo (h i) (R i) (R i)
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (fst S.toOver X.toOver ≫ f i) (snd S.toOver X.toOver ≫ π i) (τ i)

omit [NumberField.IsCMField E] in
/-- Exact native complex cohomology of the algebraic correspondence. -/
theorem surfaceCorrespondence_realize :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) 8
        (surfaceCorrespondence E H h R S X f π τ) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
        (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).toOver) 4 4
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (fst S.toOver X.toOver)
          (SurfaceConstructionQ.CM.fourCup S (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i)
            ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (τ i))))))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (snd S.toOver X.toOver)
          (SurfaceConstructionQ.CM.fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
            ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i))))))) := by
  erw [SurfaceConstructionQ.CM.schemePullback_fourCup (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (fst S.toOver X.toOver),
    SurfaceConstructionQ.CM.schemePullback_fourCup (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (snd S.toOver X.toOver)]
  apply CoefficientCups.CM.SurfaceConstruction.fourDivisorCup_realize_regroup
  intro i
  erw [SurfaceConstructionQ.CM.schemePullback_comp (fst S.toOver X.toOver) (f i) 1,
    SurfaceConstructionQ.CM.schemePullback_comp (snd S.toOver X.toOver) (π i) 1]
  exact Pairs.CM.SurfaceConstruction.normalizedOppositePair_realize E (h i) (R i) (R i)
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
    (fst S.toOver X.toOver ≫ f i) (snd S.toOver X.toOver ≫ π i) (τ i)

omit [NumberField.IsCMField E] in
theorem surfaceCorrespondence_coefficient :
    surfaceCorrespondence E H h R S X f π τ =
      CoefficientCups.CM.SurfaceConstruction.coefficientCup E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) 4 4
        (Projection.CM.SurfaceConstruction.coefficientPullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
          (fst S.toOver X.toOver) 4 (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ))
        (Projection.CM.SurfaceConstruction.coefficientPullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
          (snd S.toOver X.toOver) 4
          (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π (fun i => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i)))) := by
  apply CanonicalCoefficients.CM.SurfaceConstruction.realizeCoefficient_injective E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) 8
  refine (surfaceCorrespondence_realize E H h R S X f π τ).trans ?_
  symm
  refine (CoefficientCups.CM.SurfaceConstruction.realizeCoefficient_cup E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) 4 4 _ _).trans ?_
  refine congrArg₂ (fun a b : (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).complexCohomology 4 =>
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
      (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).toOver) 4 4 a b) ?_ ?_
  · exact (Projection.CM.SurfaceConstruction.realizeCoefficient_pullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (X := S) (fst S.toOver X.toOver) 4 _).trans
      (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (fst S.toOver X.toOver))
        (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R S f τ))
  · exact (Projection.CM.SurfaceConstruction.realizeCoefficient_pullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (X := X) (snd S.toOver X.toOver) 4 _).trans
      (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (snd S.toOver X.toOver))
        (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R X π (fun i => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i))))

omit [NumberField.IsCMField E] in
/-- Pushing the actual algebraic correspondence is multiplication by the
degree-zero class obtained by integrating the source fourfold class. -/
theorem surfaceCorrespondence_pushforward (hS : S.complexDimension = 2)
    (hX : 2 ≤ X.complexDimension) :
    (Cycles.Functoriality.UnitCap.cohomologyPushforward
      (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (snd S.toOver X.toOver)
      (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
        (snd S.toOver X.toOver)) 4 2 (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)).baseChange E
        (surfaceCorrespondence E H h R S X f π τ) =
      CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 0
        (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π (fun i => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i)))
        ((Cycles.Functoriality.UnitCap.cohomologyPushforward
          (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (snd S.toOver X.toOver)
          (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
            (snd S.toOver X.toOver)) 2 0 (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)).baseChange E
          (Projection.CM.SurfaceConstruction.coefficientPullback E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
            (fst S.toOver X.toOver) 4 (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ))) := by
  have he := (surfaceCorrespondence_coefficient E H h R S X f π τ).trans
    (CanonicalCoefficients.CM.SurfaceConstruction.coefficientCup44_comm E (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) _ _)
  exact (congrArg
    ((Cycles.Functoriality.UnitCap.cohomologyPushforward (X := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (snd S.toOver X.toOver)
      (SurfaceConstructionQ.CM.map_isProper (S := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X) (X := X)
        (snd S.toOver X.toOver)) 4 2
      (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)).baseChange E) he).trans
    (Projection.CM.SurfaceConstruction.coefficientProjection44 E (W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X)
      (snd S.toOver X.toOver) (by rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega) hX _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.Correspondence.CM.SurfaceConstruction
