import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularSections

/-! # Regular Conormal Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RegularConormalCocycle

noncomputable section

/-! Conormal transition values are original regular sections on the
actual special fiber and satisfy the ordinary restricted cocycle equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen CommonOpenCocycle.dualFamilyTripleAffineOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

def dualRegularConormalTransition (i j : U.I₀)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    Γ((DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left,
      DualAffine.RegularSections.dualAffineReducedOpen ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)) :=
  DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)
    (DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j z)

theorem dualRegularConormalTransition_cocycle (i j l : U.I₀)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
        (homOfLE ((VaryingDualReduction.dualFamilyReduction ℂ X).preimage_mono
          (show (CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 from
            inf_le_left))).op (dualRegularConormalTransition X U i j z) +
      (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
        (homOfLE ((VaryingDualReduction.dualFamilyReduction ℂ X).preimage_mono
          (show (CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U j l).1 from
            le_inf (inf_le_left.trans inf_le_right) inf_le_right))).op (dualRegularConormalTransition X U j l z) =
      (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
        (homOfLE ((VaryingDualReduction.dualFamilyReduction ℂ X).preimage_mono
          (show (CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l).1 ≤ (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i l).1 from
            le_inf (inf_le_left.trans inf_le_left) inf_le_right))).op (dualRegularConormalTransition X U i l z) := by
  have h := congrArg (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyTripleAffineOpen ℂ X U i j l))
    (DualAffine.ConormalCocycle.dualFamilyPairConormalTransition_cocycle X U i j l z)
  rw [map_add, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict,
    DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RegularConormalCocycle
