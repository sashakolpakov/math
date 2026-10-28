import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterBaseChange

noncomputable section

/-! The geometric Cartesian comparison of projective spaces is their specified relative projective base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (n : ℕ)

theorem projectiveParameter_composite_isPullback :
    IsPullback (RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) (ProjectivePresentations.projectiveSpaceOver T.left n).hom
      (ProjectivePresentations.projectiveSpaceOver S n).hom (f.left ≫ M.hom) := by
  rw [f.w]
  exact RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback T.hom n

theorem projectiveParameterBaseChangeMap_eq :
    Cartesian.BaseChangeMap.cartesianBaseChangeMap f.left M.hom (RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap M.hom n)
      (projectiveParameter_composite_isPullback f n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback M.hom n) =
        RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n := by
  symm
  apply Cartesian.BaseChangeMap.cartesianBaseChangeMap_unique
  · rw [← RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_comp, f.w]
  · exact RelativeProjective.BaseMaps.relativeProjectiveBaseMap_over f.left n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterBaseChange
