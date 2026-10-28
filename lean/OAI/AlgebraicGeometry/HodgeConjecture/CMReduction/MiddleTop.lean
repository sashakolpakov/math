import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.GeometricPairing
import OAI.AlgebraicGeometry.HodgeConjecture.Kunneth

/-! # Middle Top -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MiddleTop.CM.Construction

noncomputable section

/-! Each old CM factor contributes its literal nonzero top-degree class,
obtained by cupping the opposite H1 vectors against the ample power. -/

open _root_.CategoryTheory

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

omit [NumberField.IsCMField E] in
theorem realizedVector_ne_zero {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (τ : Gal(E/ℚ)) : Endpoints.CM.Construction.realizedVector E R τ ≠ 0 :=
  R.complexComparison.map_ne_zero_iff.mpr
    (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ))

omit [NumberField.IsCMField E] in
theorem realization_dimension_pos {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) :
    0 < R.abelianVariety.variety.complexDimension := by
  have h := Kunneth.CM.SurfaceConstruction.complex_degree_le R.abelianVariety.variety 1
    (Endpoints.CM.Construction.realizedVector E R 1) (realizedVector_ne_zero E R 1)
  omega

def middleTopClass (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) :
    R.abelianVariety.variety.complexCohomology
      (R.abelianVariety.variety.complexDimension + R.abelianVariety.variety.complexDimension) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace R.abelianVariety.toOver))
    (ModuleCat.of ℂ ℂ) (by have := realization_dimension_pos E R; omega)
    (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup R.abelianVariety.variety
      (R.abelianVariety.variety.complexDimension - 1)
      (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) (Endpoints.CM.Construction.realizedVector E R 1))

theorem cohomologyCast_injective {K : Type} [CommRing K] (X : TopCat.{0})
    {n m : ℕ} (h : n = m) :
    Function.Injective (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of K K) h) := by
  subst m
  exact Function.injective_id

theorem middleTopClass_ne_zero (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput) (v : Pairing.CM.Construction.SignType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) : middleTopClass E v R ≠ 0 := by
  let σ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1
  let τ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
  have hconj : τ = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ := by
    simpa only [mul_one] using ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1
  have hback : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ = σ := by rw [hconj, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
  have hn := GeometricPairing.CM.Construction.geometric_opposite_pairing_ne_zero R h_PolarizedPairing
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E v)
    (R.abelianVariety.variety.complexDimension - 1)
    (by rw [R.abelianVariety.variety.analyticModel_complex_finrank]
        have := realization_dimension_pos E R
        omega)
    τ (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E σ)
    ((ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E E τ _).mpr (fun a => ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_eigen E a τ))
    (by rw [hback]
        exact (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E E σ _).mpr (fun a => ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_eigen E a σ))
    (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E τ) (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E σ)
  intro hz
  unfold middleTopClass at hz
  apply hn
  exact cohomologyCast_injective (K := ℂ) (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) _
    (hz.trans (map_zero _).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MiddleTop.CM.Construction
