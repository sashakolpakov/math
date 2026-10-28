import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.CechCycle

/-! # Conormal Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ConormalCocycle

noncomputable section

/-! The constructed linear tangent cocycle has native conormal
coordinates on the fixed fiber, and those coordinates satisfy the
actual restricted triple-intersection equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverPairAffineOpen Family.AffineCoverIntersections.familyCoverTripleAffineOpen
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberTensorAlgebras Affine.OpenDiagram.familyAffineCoordinateFunctor
attribute [local implicit_reducible] HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv

def familyTangentConormalPair (i j : U.I₀) : Derivation ℂ R ℂ →ₗ[ℂ]
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ]
      ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)) :=
  (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)).toLinearMap.comp
    (CechCycle.familyTangentPair ℂ R X U i j)

theorem familyTangentConormalPair_cocycle (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) (i j l : U.I₀) :
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from
        inf_le_left) (familyTangentConormalPair R X U i j d z) +
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (familyTangentConormalPair R X U j l d z) =
    FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i l).1 from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (familyTangentConormalPair R X U i l d z) := by
  have h := congrArg (fun v => FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l) v z)
    (LinearMap.congr_fun (CechCycle.familyTangentPair_restricted_cocycle ℂ R X U i j l) d)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at h
  rw [map_add, LinearMap.add_apply, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural,
    FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural, FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv_natural] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ConormalCocycle
