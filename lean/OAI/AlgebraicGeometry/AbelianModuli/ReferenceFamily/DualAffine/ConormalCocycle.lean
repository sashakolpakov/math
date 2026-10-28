import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.TransitionCocycle

/-! # Conormal Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCocycle

noncomputable section

/-! The original transition maps give a regular-function-valued
conormal cocycle on the actual affine pair and triple intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Dual.CommonOpenCocycle.dualFamilyPairAffineOpen Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

def dualFamilyPairConormalTransition (i j : U.I₀) :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ]
      HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)) :=
  ConormalCoordinates.dualAffineConormalLinearEquiv X (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)
    (Dual.CommonOpenCocycle.dualFamilyPairTransitionDerivation ℂ X U i j)

theorem dualFamilyPairConormalTransition_cocycle (i j l : U.I₀)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 from
          inf_le_left) (dualFamilyPairConormalTransition X U i j z) +
      Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U j l).1 from
          le_inf (inf_le_left.trans inf_le_right) inf_le_right) (dualFamilyPairConormalTransition X U j l z) =
      Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
        (show (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (Dual.CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i l).1 from
          le_inf (inf_le_left.trans inf_le_left) inf_le_right) (dualFamilyPairConormalTransition X U i l z) := by
  have h := congrArg (fun d => ConormalCoordinates.dualAffineConormalLinearEquiv X (Dual.CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l) d z)
    (TransitionCocycle.dualFamilyPairTransition_restricted_cocycle ℂ X U i j l)
  rw [map_add, LinearMap.add_apply, ConormalCoordinates.dualAffineConormalLinearEquiv_natural,
    ConormalCoordinates.dualAffineConormalLinearEquiv_natural, ConormalCoordinates.dualAffineConormalLinearEquiv_natural] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCocycle
