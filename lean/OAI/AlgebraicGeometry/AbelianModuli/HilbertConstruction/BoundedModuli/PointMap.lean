import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.UniversalMap

/-! # Point Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointMap

noncomputable section

/-! The complete universal moduli isomorphism gives a specified map on each test scheme's parameter points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def boundedPolarizedLevelUniversalPointMap
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    (T : Over S) :
    (T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) → Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) :=
  fun c => Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE)

theorem boundedPolarizedLevelUniversalPointMap_abelian
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    (T : Over S) (c : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) :
    (boundedPolarizedLevelUniversalPointMap A B j P PB PD PE T c).abelian.hom =
      (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T
        (c ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)).val.val.val := by
  change (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE)).abelian.hom = _
  exact UniversalMap.boundedPolarizedLevelUniversalIso_point_abelian A B j P PB PD PE c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointMap
