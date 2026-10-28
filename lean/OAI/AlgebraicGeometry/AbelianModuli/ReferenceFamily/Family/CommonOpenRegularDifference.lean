import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle

/-! # Common Open Regular Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenRegularDifference

noncomputable section

/-! The original common-open tangent differences define actual
regular sections on the fixed fiber, compatibly with every further
affine restriction and with the original cover's pair sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberTensorAlgebras Affine.OpenDiagram.familyAffineCoordinateFunctor
attribute [local implicit_reducible] HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv CommonOpenTangentDifferences.familyCommonOpenTangentDifference

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

def familyCommonOpenRegularDifference {V W Z : X.left.affineOpens}
    (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V) :=
  FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V
    (CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X h j d) z)

theorem familyCommonOpenRegularDifference_restrict {U V W Z : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (j : V.1 ≤ Z.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    familyCommonOpenRegularDifference R X (t.trans h) (t.trans j) d z =
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE ((FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X).preimage_mono t)).op
        (familyCommonOpenRegularDifference R X h j d z) := by
  have hd := LinearMap.congr_fun (FamilyTangent.DifferenceNaturality.familyCommonOpenTangentDifference_restrict ℂ R X t h j) d
  simp only [LinearMap.comp_apply] at hd
  unfold familyCommonOpenRegularDifference
  rw [← hd, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict]
  rfl

theorem familyTangentRegularPair_commonOpen [IsSeparated X.hom] (U : X.left.AffineOpenCover)
    (d : Derivation ℂ R ℂ) (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d z i j =
      familyCommonOpenRegularDifference R X
        (V := AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) (W := AffineCoverIntersections.familyCoverAffineOpen R X U i)
        (Z := AffineCoverIntersections.familyCoverAffineOpen R X U j) inf_le_left inf_le_right d z := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenRegularDifference
