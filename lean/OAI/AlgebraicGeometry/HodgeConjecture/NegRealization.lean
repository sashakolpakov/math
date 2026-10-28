import OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients

/-! # Neg Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.NegRealization.CM.SurfaceConstruction

noncomputable section

/-! Negating a CM type changes its rational marking by the field's
complex conjugation, retaining the supplied abelian variety. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def fieldConjugationMap : E ≃ₗ[ℚ] E := (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E).toLinearEquiv

omit [IsGalois ℚ E] in
theorem fieldConjugation_coordinates (x : ComplexMultiplication.WeightOne.CM.Complexification E) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E ((fieldConjugationMap E).toLinearMap.baseChange ℂ x) τ =
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul,
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul]
    change a * τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) = a * (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) x
    exact congrArg (fun z => a * z)
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E τ.toRingHom x)

omit [IsGalois ℚ E] in
theorem fieldConjugation_embeddingVector (τ : E →ₐ[ℚ] ℂ) :
    (fieldConjugationMap E).toLinearMap.baseChange ℂ (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) =
      ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  classical
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  funext σ
  rw [fieldConjugation_coordinates, ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ = τ
  · have h' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ = σ := by rw [← h, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    simp [h, h']
  · have h' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ ≠ σ := by
      intro he
      apply h
      rw [← he, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    simp [h, h']

theorem fieldConjugation_subspace
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (b : Bool) (x : ComplexMultiplication.WeightOne.CM.Complexification E) :
    (fieldConjugationMap E).toLinearMap.baseChange ℂ x ∈
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v).subspace b ↔
      x ∈ (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v.neg).subspace b := by
  rw [ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mem_subspace_iff, ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mem_subspace_iff]
  constructor
  · intro hx σ hσ
    have hc := hx (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ)
    rw [fieldConjugation_coordinates, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive] at hc
    have hh := hc hσ
    rw [(ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v).property] at hh
    exact hh
  · intro hx σ hσ
    rw [fieldConjugation_coordinates] at hσ
    have hh := hx (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) hσ
    change Bool.not ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v).val (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ)) = b at hh
    rw [(ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v).property, Bool.not_not] at hh
    exact hh

def negRealization
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v.neg) where
  abelianVariety := R.abelianVariety
  comparison := (fieldConjugationMap E).trans R.comparison
  holomorphic x := by
    change (R.comparison.toLinearMap.comp (fieldConjugationMap E).toLinearMap).baseChange ℂ x ∈ _ ↔ _
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply, R.holomorphic]
    exact fieldConjugation_subspace E v true x
  antiholomorphic x := by
    change (R.comparison.toLinearMap.comp (fieldConjugationMap E).toLinearMap).baseChange ℂ x ∈ _ ↔ _
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply, R.antiholomorphic]
    exact fieldConjugation_subspace E v false x

theorem negRealization_complexComparison
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (x : ComplexMultiplication.WeightOne.CM.Complexification E) :
    (negRealization E v R).complexComparison x =
      R.complexComparison ((fieldConjugationMap E).toLinearMap.baseChange ℂ x) := by
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) 1
    ((R.comparison.toLinearMap.comp (fieldConjugationMap E).toLinearMap).baseChange ℂ x) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  rfl

theorem negRealization_embeddingVector
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    (τ : E →ₐ[ℚ] ℂ) :
    (negRealization E v R).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) =
      R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)) := by
  rw [negRealization_complexComparison, fieldConjugation_embeddingVector]

theorem negRealization_at_one
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    (negRealization E v R).complexComparison
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) =
      R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))) := by
  rw [negRealization_embeddingVector]
  exact congrArg (fun τ => R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ))
    (by simpa only [mul_one] using (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1).symm)

theorem negRealization_at_conjugation
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    (negRealization E v R).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))) =
      R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) := by
  rw [negRealization_embeddingVector]
  have hc : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) =
      ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) := by
    simpa only [mul_one] using ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1
  rw [hc, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]

end

end OAI.AlgebraicGeometry.HodgeConjecture.NegRealization.CM.SurfaceConstruction
