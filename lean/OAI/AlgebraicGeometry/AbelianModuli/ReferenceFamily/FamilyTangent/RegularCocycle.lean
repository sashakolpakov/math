import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.CechCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants

/-! # Regular Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle

noncomputable section

/-! Evaluation of the linear tangent cocycle on a native conormal
vector gives original regular sections on the fixed-fiber cover. These
sections form a cocycle and are linear in both arguments. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverPairAffineOpen Family.AffineCoverIntersections.familyCoverTripleAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv

def familyTangentRegularPair (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j) :=
  FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)
    (ConormalCocycle.familyTangentConormalPair R X U i j d z)

theorem familyTangentRegularPair_cocycle (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    RegularPair.Closed.RegularPairCocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
      (familyTangentRegularPair R X U d z) := by
  intro i j l
  have h := congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l))
    (ConormalCocycle.familyTangentConormalPair_cocycle R X U d z i j l)
  rw [map_add, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict, FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict,
    FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict] at h
  exact h

theorem familyTangentRegularPair_add_tangent (d e : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    familyTangentRegularPair R X U (d + e) z i j =
      familyTangentRegularPair R X U d z i j + familyTangentRegularPair R X U e z i j :=
  (congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
    (LinearMap.congr_fun ((ConormalCocycle.familyTangentConormalPair R X U i j).map_add d e) z)).trans (map_add _ _ _)

theorem familyTangentRegularPair_add_conormal (d : Derivation ℂ R ℂ)
    (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    familyTangentRegularPair R X U d (z + w) i j =
      familyTangentRegularPair R X U d z i j + familyTangentRegularPair R X U d w i j :=
  (congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
    ((ConormalCocycle.familyTangentConormalPair R X U i j d).map_add z w)).trans (map_add _ _ _)

theorem familyTangentRegularPair_smul_tangent (c : ℂ) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    familyTangentRegularPair R X U (c • d) z i j =
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE (show Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j ≤ ⊤ from le_top)).op
          (Open.ComplexConstants.complexGlobalSectionMap (TangentBasePoint.fixedFamilyFiber ℂ R X) c) * familyTangentRegularPair R X U d z i j :=
  (congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
    (LinearMap.congr_fun ((ConormalCocycle.familyTangentConormalPair R X U i j).map_smul c d) z)).trans
      (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_smul R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) c _)

theorem familyTangentRegularPair_smul_conormal (c : ℂ) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j : U.I₀) :
    familyTangentRegularPair R X U d (c • z) i j =
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE (show Fixed.CechCover.fixedFamilyCechCover ℂ R X U i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X U j ≤ ⊤ from le_top)).op
          (Open.ComplexConstants.complexGlobalSectionMap (TangentBasePoint.fixedFamilyFiber ℂ R X) c) * familyTangentRegularPair R X U d z i j :=
  (congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
    ((ConormalCocycle.familyTangentConormalPair R X U i j d).map_smul c z)).trans
      (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_smul R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) c _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularCocycle
