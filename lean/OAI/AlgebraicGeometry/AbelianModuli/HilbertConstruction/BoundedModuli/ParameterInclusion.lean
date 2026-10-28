import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection

/-! # Parameter Inclusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ParameterInclusion

noncomputable section

/-! The inclusion of the combined bounded locus is a monomorphism in the category of parameter schemes over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedPolarizedLevelIsoParameterInclusion_mono
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) : Mono (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P) :=
  Functor.mono_of_mono_map (Over.forget S)
    (inferInstanceAs (Mono (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ParameterInclusion
