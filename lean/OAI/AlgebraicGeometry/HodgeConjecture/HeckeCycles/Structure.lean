import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.InputAssembly
import OAI.NumberTheory.PadicHodge.FrobeniusSlope
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Definitions

/-! # Structure -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Structure

/-! HeckeCycles for the original source family and fixed theta input. Every
former theorem input is supplied by a proof; the source predicate,
canonical Hodge structure and all sufficiently divisible levels remain. -/
open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
theorem extraction_of_prescribed_cm_hodge_structure
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (d : Gal(E/ℚ) → Bool) (hd : ∀ τ, d τ = v.val τ⁻¹)
    (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, Albanese.Definitions.CM.HodgeComparison.IsCanonicalH1 (X N) (H N))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
 :
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N, 0 < N → N₀ ∣ N → Θ N ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (H N) := by
  have h43 : Moduli.CM.ReferenceFamilyInput := PELModuli.IntegralModel.ReferenceFamilyConstructed.provedReferenceFamilyModuliInput
  have h44 : ArithmeticModels.CM.IntegralModelInput :=
    PELModuli.IntegralModel.ProjectiveModelsAlbanese.projective_models_and_albanese_generation_unconditional
  have h419 : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput := by
    intro K instField instNumberField
    exact @NumberTheory.PadicHodge.FrobeniusSlope.full_comparison_input K instField instNumberField
  exact Constructed.InputAssembly.CM.extraction_from_remaining_inputs
    E v hv d hd Nbase hNbase X H hH Θ hsource h43 h44 h419

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Structure

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Structure.CM

/-! The HeckeCycles statement, with its proof supplied by the completed development. -/

/-- HeckeCycles: extraction of the prescribed CM Hodge structure,
stated for one multiplicity line and one fixed theta input. -/
theorem extraction_of_prescribed_cm_hodge_structure
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true)
    (d : Gal(E/ℚ) → Bool)
    (hd : ∀ τ, d τ = v.val (τ⁻¹))
    (Nbase : ℕ)
    (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N : ℕ,
      ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, Albanese.Definitions.CM.HodgeComparison.IsCanonicalH1 (X N) (H N))
    (Θ : ∀ N : ℕ,
      ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : Definitions.CM.IsSourceBallThetaFamily E d Nbase X Θ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        Θ N ∈ Submodule.span ℂ
          {z | ∃ f : E →ₗ[ℚ] (X N).rationalCohomology 1,
            ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) (H N) f ∧
            ∃ u : ComplexMultiplication.WeightOne.CM.Complexification E,
              u ∈ (ℂ ∙ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) ∧
              f.baseChange ℂ u = z} := by
  exact Structure.extraction_of_prescribed_cm_hodge_structure
    E v hv d hd Nbase hNbase X H hH Θ hsource

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Structure.CM

end

end OAI
