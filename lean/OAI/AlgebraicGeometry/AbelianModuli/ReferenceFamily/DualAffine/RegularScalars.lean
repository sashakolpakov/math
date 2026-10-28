import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateComplexConstants

/-! # Regular Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularScalars

noncomputable section

/-! Complex scalar multiplication on the actual affine coefficient
rings becomes multiplication by the original restricted global constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over (Spec (.of (DualNumber ℂ))))
    [IsIntegral (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] (V : X.left.affineOpens)

theorem dualAffineRegularSectionEquiv_constant (c : ℂ) :
    RegularSections.dualAffineRegularSectionEquiv ℂ X V
      (algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)) c) =
    (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
      (homOfLE (show RegularSections.dualAffineReducedOpen ℂ X V ≤ ⊤ from le_top)).op
        (Open.ComplexConstants.complexGlobalSectionMap (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c) := by
  let Y := Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V
  let i := ConormalInclusions.dualAffineCommonOpenInclusion ℂ X V
  have : Smooth (i.left ≫ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom) := inferInstance
  have : Smooth Y.hom := (congrArg Smooth i.w).mp this
  have : IsReduced Y.left := isReduced_of_isOpenImmersion i.left
  have hc : algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) c =
      i.left.appTop (Open.ComplexConstants.complexGlobalSectionMap (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c) :=
    (Affine.CoordinateComplexConstants.affineCoordinateComplexConstant Y c).trans (Affine.CoordinateComplexConstants.complexGlobalSectionMap_natural i c).symm
  have h := Open.ImmersionGlobalSections.openImmersionTopSection_global i.left (Open.ComplexConstants.complexGlobalSectionMap (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c)
  change Regular.SectionTransport.regularSectionTransport (RegularSections.dualAffineCommonOpenInclusion_range ℂ X V)
    ((IsOpenImmersion.ΓIsoTop i.left).hom (algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) c)) = _
  rw [hc]
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (RegularSections.dualAffineCommonOpenInclusion_range ℂ X V)) h).trans
    (Regular.SectionTransport.regularSectionTransport_restrict rfl (RegularSections.dualAffineCommonOpenInclusion_range ℂ X V) le_top le_top _)

theorem dualAffineRegularSectionEquiv_smul (c : ℂ)
    (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)) :
    RegularSections.dualAffineRegularSectionEquiv ℂ X V (c • a) =
      (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
        (homOfLE (show RegularSections.dualAffineReducedOpen ℂ X V ≤ ⊤ from le_top)).op
          (Open.ComplexConstants.complexGlobalSectionMap (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c) * RegularSections.dualAffineRegularSectionEquiv ℂ X V a := by
  rw [Algebra.smul_def, map_mul, dualAffineRegularSectionEquiv_constant]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularScalars
