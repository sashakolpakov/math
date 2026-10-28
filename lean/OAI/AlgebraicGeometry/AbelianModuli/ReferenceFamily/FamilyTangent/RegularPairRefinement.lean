import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenRegularDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement

/-! # Regular Pair Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularPairRefinement

noncomputable section

/-! Refinement of the family's original regular tangent pair cocycle
is exactly the common-open tangent difference of the original parent
charts on each affine overlap of the refining cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberTensorAlgebras Affine.OpenDiagram.familyAffineCoordinateFunctor
attribute [local implicit_reducible] HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    (U D : X.left.AffineOpenCover) (r : D.I₀ → U.I₀)
    (hr : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)).1)

include hr

theorem fixedFamilyCechCover_refinement (i : D.I₀) :
    Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ≤ Fixed.CechCover.fixedFamilyCechCover ℂ R X U (r i) :=
  (FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X).preimage_mono (hr i)

variable [Algebra ℂ R] [IsScalarTower ℂ R ℂ] [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

theorem familyTangentRegularPair_refinement (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : D.I₀) :
    RegularPair.Refinement.regularPairRefinement (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
        (Fixed.CechCover.fixedFamilyCechCover ℂ R X D) r (fixedFamilyCechCover_refinement R X U D r hr)
        (RegularCocycle.familyTangentRegularPair R X U d z) i j =
      Family.CommonOpenRegularDifference.familyCommonOpenRegularDifference R X (V := Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j)
        (W := Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)) (Z := Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r j))
        (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j)) d z :=
  (Family.CommonOpenRegularDifference.familyCommonOpenRegularDifference_restrict R X
    (U := Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j) (V := Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U (r i) (r j))
    (W := Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)) (Z := Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r j))
    (inf_le_inf (hr i) (hr j)) inf_le_left inf_le_right d z).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularPairRefinement
