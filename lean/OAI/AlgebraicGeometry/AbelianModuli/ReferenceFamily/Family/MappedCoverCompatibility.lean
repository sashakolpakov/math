import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.OpenIntersectionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections

/-! # Mapped Cover Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCompatibility

noncomputable section

/-! Agreement on actual affine intersections gives the literal
pullback compatibility required to glue maps after a functor preserving
pullbacks, such as either of the base changes used for a tangent family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) {S : Scheme} (F : Over (Spec (.of R)) ⥤ Over S)
    [PreservesLimitsOfShape WalkingCospan F] (Y : Over S)
    (f : ∀ i : U.I₀, F.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverAffineOpen R X U i)) ⟶ Y)

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen Affine.OpenDiagram.familyAffineOpenDiagram

theorem familyMappedCover_compatible
    (h : ∀ i j : U.I₀,
      F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
        (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)) ≫ f i =
      F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
        (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right)) ≫ f j)
    (i j : U.I₀) :
    pullback.fst (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left
        (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U j).1)).left ≫ (f i).left =
      pullback.snd _ _ ≫ (f j).left := by
  have hp : IsPullback
      (F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
        (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left))).left
      (F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
        (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right))).left
      (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left
      (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U j).1)).left :=
    ((OpenIntersectionPullback.familyOpenIntersection_isPullback X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1
      (AffineCoverIntersections.familyCoverAffineOpen R X U j).1).map F).map (Over.forget S)
  apply (cancel_epi hp.isoPullback.hom).mp
  rw [← Category.assoc, hp.isoPullback_hom_fst, ← Category.assoc, hp.isoPullback_hom_snd]
  exact congrArg Over.Hom.left (h i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCompatibility
