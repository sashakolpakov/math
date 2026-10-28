import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover

/-! # Mapped Cover Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCoverage

noncomputable section

/-! The original affine cover still covers after either base change
used in the tangent construction. The statements retain the literal
functor maps as the cover inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem familyAffineCover_inclusions_covers (R : Type) [CommRing R]
    (X : Over (Spec (.of R))) (U : X.left.AffineOpenCover) (x : X.left) :
    ∃ i : U.I₀, x ∈ (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1).left.opensRange := by
  refine ⟨U.idx x, ?_⟩
  change x ∈ (AffineCoverIntersections.familyCoverAffineOpen R X U (U.idx x)).1.ι.opensRange
  rw [Scheme.Opens.opensRange_ι]
  exact U.covers x

local instance mappedCover_open {B C : Scheme} (f : B ⟶ C)
    {X Y : Over C} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    IsOpenImmersion ((Over.pullback f).map i).left := OverPullbackCartesianMap.overPullback_map_open f i

theorem overPullback_indexed_covers {B C : Scheme} (f : B ⟶ C) {I : Type}
    {X : Over C} (A : I → Over C) (i : ∀ j, A j ⟶ X) [∀ j, IsOpenImmersion (i j).left]
    (hc : ∀ x : X.left, ∃ j, x ∈ (i j).left.opensRange)
    (x : ((Over.pullback f).obj X).left) :
    ∃ j, x ∈ (((Over.pullback f).map (i j)).left).opensRange := by
  obtain ⟨j, hj⟩ := hc (pullback.fst X.hom f x)
  refine ⟨j, ?_⟩
  rw [OverPullbackOpenCover.overPullback_map_opensRange]
  exact hj

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCoverage
