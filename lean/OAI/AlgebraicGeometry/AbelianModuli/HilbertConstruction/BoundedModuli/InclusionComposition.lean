import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection

/-! # Inclusion Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.InclusionComposition

noncomputable section

/-! Composing a point with the combined parameter inclusion factors through its polarization projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedPolarizedLevelIsoParameterInclusion_comp
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) {T : Over S} (c : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) :
    c ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P =
      (c ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterToPolarization A B j P) ≫
        Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P := by
  unfold Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion
  exact (Category.assoc c (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterToPolarization A B j P)
    (Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.InclusionComposition
