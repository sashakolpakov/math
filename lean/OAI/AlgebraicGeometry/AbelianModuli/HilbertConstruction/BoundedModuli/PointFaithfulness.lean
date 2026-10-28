import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterClassifierFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ParameterInclusion

/-! # Point Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointFaithfulness

noncomputable section

/-! Distinct points of the combined bounded parameter cannot classify the same complete moduli isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedPolarizedLevelUniversalIso_points_injective
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    (T : Over S) :
    Function.Injective (PointMap.boundedPolarizedLevelUniversalPointMap A B j P PB PD PE T) := by
  intro c d h
  have := ParameterInclusion.boundedPolarizedLevelIsoParameterInclusion_mono A B j P
  apply (cancel_mono (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)).mp
  apply ParameterClassifierFaithfulness.boundedAbelianIsoParameter_point_injective A.abelian B.abelian j P T
  exact (PointMap.boundedPolarizedLevelUniversalPointMap_abelian A B j P PB PD PE T c).symm.trans
    ((congrArg (fun e => e.abelian.hom) h).trans
      (PointMap.boundedPolarizedLevelUniversalPointMap_abelian A B j P PB PD PE T d))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointFaithfulness
