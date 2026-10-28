import OAI.AlgebraicGeometry.HodgeConjecture.Pairs
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Descent

/-! # Opposite Pairs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs.CM.Construction

noncomputable section

/-! Unchanged slots of a CMReduction transition give actual algebraic divisors.
The existing coefficient-field pair construction is specialized to the
explicit ScalarDescent and Lefschetz inputs, then included in complex cohomology. -/

open _root_.CategoryTheory
open scoped TensorProduct

theorem coefficient_algebraic_realize
    (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    {x : E ⊗[ℚ] X.rationalCohomology (p + p)}
    (hx : x ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X (p + p) x ∈
      X.complexGeometricAlgebraicClasses p := by
  obtain ⟨n, a, Z, hz⟩ := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_finite_sum E X p hx
  rw [← hz]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Descent.CM.Construction.rational_algebraic_complex_inclusion X p _ ⟨Z i, rfl⟩

theorem canonical_opposite_pair_algebraic
    (h_ScalarDescent : Descent.CM.Construction.ScalarDescentInput) (h_DegreeTwo : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : X.toOver ⟶ R.abelianVariety.toOver)
    (πT : X.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πR
        (R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ)))
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πT
        (T.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)))) ∈
      X.complexGeometricAlgebraicClasses 1 := by
  rw [← Pairs.CM.SurfaceConstruction.normalizedOppositePair_realize E h R T X πR πT τ]
  apply coefficient_algebraic_realize
  apply Pairs.CM.SurfaceConstruction.normalizedOppositePair_algebraic E (h_ScalarDescent E)
    (fun V a ha => h_DegreeTwo V ha) h R T X πR πT τ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs.CM.Construction
