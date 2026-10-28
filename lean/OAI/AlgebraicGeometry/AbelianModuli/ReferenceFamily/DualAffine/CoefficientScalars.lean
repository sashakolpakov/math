import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarSectionValues

/-! # Coefficient Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientScalars

noncomputable section

/-! On the actual affine dual-number family, scalar pullback fixes
the regular constant coefficient and multiplies the first-order coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualAffineSectionCoefficients_scalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (c : ℂ)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    SectionCoefficients.dualAffineSectionCoefficients X ((Dual.Scalars.dualFamilyScalar X c).left.appTop s) =
      Dual.CoefficientScalars.dualCoefficientScale (algebraMap ℂ Γ(X.left, ⊤) c) (SectionCoefficients.dualAffineSectionCoefficients X s) := by
  apply CoefficientNaturality.dualRegularCoefficient_ext X
  intro p
  have h₁ := SectionCoefficients.dualAffineSectionCoefficients_evaluation X p ((Dual.Scalars.dualFamilyScalar X c).left.appTop s)
  have h₂ := Dual.ScalarSectionValues.dualConstantPoint_scalar_section X c p s
  have h₃ := congrArg (LieRanks.dualNumberScale ℂ c) (SectionCoefficients.dualAffineSectionCoefficients_evaluation X p s)
  have h₄ := Dual.CoefficientScalars.dualCoefficientScale_complex (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) c (SectionCoefficients.dualAffineSectionCoefficients X s)
  exact h₁.symm.trans (h₂.trans (h₃.trans h₄.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientScalars
