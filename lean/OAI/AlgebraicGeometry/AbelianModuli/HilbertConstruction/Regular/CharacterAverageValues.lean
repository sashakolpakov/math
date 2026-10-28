import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverages

/-! # Character Average Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverageValues

noncomputable section

/-! The regular character average acts on actual functions by the finite weighted translation formula. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    (R : Type w) [CommRing R] [Algebra K R]

theorem regularCharacterAverage_apply (χ : G →* Kˣ) (v : G → R) (b : G) :
    CharacterAverages.regularCharacterAverage K G R χ v b =
      algebraMap K R ((Fintype.card G : K)⁻¹) *
        ∑ a : G, algebraMap K R ((χ a : K)⁻¹) * v (b * a) := by
  simp only [CharacterAverages.regularCharacterAverage, CharacterWeightedOperators.characterAverageOperator, CharacterWeightedOperators.characterWeightedOperator,
    LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply,
    TranslationRepresentation.regularTranslationRepresentation_apply]
  simp only [Algebra.smul_def]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverageValues
