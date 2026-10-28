import OAI.AlgebraicGeometry.HodgeConjecture.CoefficientCups
import Mathlib.RingTheory.Flat.Basic
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Canonical Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients.CM.SurfaceConstruction

noncomputable section

/-! The exact canonical embedding vectors and their fourfold cup are
defined over E, using the fixed comparison of each supplied realization. -/

open _root_.CategoryTheory
open scoped TensorProduct

theorem realizeCoefficient_injective (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Function.Injective (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n) := by
  let : FiniteDimensional ℚ (X.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X n
  apply (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace X.toOver) n).comp
  exact TensorProduct.map_injective_of_flat_flat E.val.toLinearMap LinearMap.id
    (fun _ _ h => Subtype.ext h) Function.injective_id

theorem coefficientCup44_comm (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a b : E ⊗[ℚ] X.rationalCohomology 4) :
    CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 4 a b = CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 4 b a := by
  apply realizeCoefficient_injective E X 8
  erw [CoefficientCups.CM.SurfaceConstruction.realizeCoefficient_cup E X 4 4, CoefficientCups.CM.SurfaceConstruction.realizeCoefficient_cup E X 4 4]
  exact CupRegrouping.CM.SurfaceConstruction.cup44_comm _ _ _

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E]
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
  (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : X.toOver ⟶ R.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ)

def canonicalEmbeddingCoefficient : E ⊗[ℚ] X.rationalCohomology 1 :=
  ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) τ (h.equivField 1) •
    Pairs.CM.SurfaceConstruction.pulledEmbeddingCoefficient E h R X π τ

theorem canonicalEmbeddingCoefficient_realize :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 1 (canonicalEmbeddingCoefficient E h R X π τ) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 π
        (R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ)) := by
  rw [canonicalEmbeddingCoefficient, Pairs.CM.SurfaceConstruction.realizeCoefficient_smul,
    Pairs.CM.SurfaceConstruction.pulledEmbeddingCoefficient_realize, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding_coe,
    Pairs.CM.SurfaceConstruction.field_embeddingVector_normalization E h τ]
  simp only [map_smul]

theorem canonicalEmbeddingCoefficient_conjugate (σ : Gal(E/ℚ)) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 1) σ
      (canonicalEmbeddingCoefficient E h R X π τ) =
      canonicalEmbeddingCoefficient E h R X π
        (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ τ) := by
  rw [canonicalEmbeddingCoefficient, ComplexMultiplication.ScalarDescent.CM.scalarConjugate_smul,
    Pairs.CM.SurfaceConstruction.pulledEmbeddingCoefficient_conjugate, canonicalEmbeddingCoefficient,
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding_galois]

def canonicalFourCoefficient (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin 4 → E →ₐ[ℚ] ℂ) : E ⊗[ℚ] X.rationalCohomology 4 :=
  CoefficientCups.CM.SurfaceConstruction.coefficientFourCup E X (fun i => canonicalEmbeddingCoefficient E (h i) (R i) X (π i) (τ i))

theorem canonicalFourCoefficient_realize (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin 4 → E →ₐ[ℚ] ℂ) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 (canonicalFourCoefficient E H h R X π τ) =
      SurfaceConstructionQ.CM.fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
        ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (τ i)))) := by
  rw [canonicalFourCoefficient, CoefficientCups.CM.SurfaceConstruction.realizeCoefficient_fourCup]
  simp only [canonicalEmbeddingCoefficient_realize]

theorem canonicalFourCoefficient_conjugate (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin 4 → E →ₐ[ℚ] ℂ) (σ : Gal(E/ℚ)) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 4) σ (canonicalFourCoefficient E H h R X π τ) =
      canonicalFourCoefficient E H h R X π (fun i =>
        ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ (τ i)) := by
  refine (CoefficientCups.CM.SurfaceConstruction.coefficientFourCup_conjugate E X
    (fun i => canonicalEmbeddingCoefficient E (h i) (R i) X (π i) (τ i)) σ).trans ?_
  apply congrArg (CoefficientCups.CM.SurfaceConstruction.coefficientFourCup E X)
  funext i
  exact canonicalEmbeddingCoefficient_conjugate E (h i) (R i) X (π i) (τ i) σ

theorem galoisCoefficientEmbedding_conjugation [NumberField.IsCMField E]
    (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) τ = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ := by
  ext x
  change (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) τ x) : ℂ) = _
  rw [ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients.CM.SurfaceConstruction
