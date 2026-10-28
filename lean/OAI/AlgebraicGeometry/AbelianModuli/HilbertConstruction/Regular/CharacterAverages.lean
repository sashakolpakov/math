import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAverageIdempotents
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.TranslationRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterProjectionRange

/-! # Character Averages -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverages

noncomputable section

/-! The basis-independent character average on regular functions is exactly the explicit rank-one character projector. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (R : Type w) [CommRing R] [Algebra K R]

def regularCharacterAverage (χ : G →* Kˣ) : Module.End R (G → R) :=
  CharacterWeightedOperators.characterAverageOperator K G (Module.End R (G → R)) (TranslationRepresentation.regularTranslationRepresentation R G) χ

theorem regularCharacterAverage_eq_projector (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) :
    regularCharacterAverage K G R χ = CharacterProjectors.regularCharacterProjector K G R χ := by
  classical
  apply (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).ext
  intro ψ
  have h := CharacterAverageIdempotents.characterAverageOperator_mul_eigen K G (Module.End R (G → R))
    (TranslationRepresentation.regularTranslationRepresentation R G) χ ψ (CharacterProjectors.regularCharacterProjector K G R ψ) hG
    (TranslationRepresentation.regularTranslation_characterProjector K G R ψ)
  have hv := congrArg (fun t : Module.End R (G → R) => t (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R ψ)) h
  by_cases hψ : ψ = χ
  · simpa [regularCharacterAverage, Module.End.mul_apply, CharacterProjectors.regularCharacterProjector_basis, hψ] using hv
  · simpa [regularCharacterAverage, Module.End.mul_apply, CharacterProjectors.regularCharacterProjector_basis, hψ] using hv

def regularCharacterAverageRangeEquiv (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) :
    (regularCharacterAverage K G R χ).range ≃ₗ[R] R :=
  LinearEquiv.ofEq _ _ (congrArg LinearMap.range (regularCharacterAverage_eq_projector K G R χ hG)) ≪≫ₗ
    CharacterProjectionRange.regularCharacterProjectorRangeEquiv K G R χ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverages
