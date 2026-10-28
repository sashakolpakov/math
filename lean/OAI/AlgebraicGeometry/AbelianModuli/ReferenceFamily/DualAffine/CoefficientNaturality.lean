import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.SectionCoefficients
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConstantPointNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.TopSectionValues

/-! # Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality

noncomputable section

/-! The actual dual-number coefficients commute with pullback between
affine schemes. Equality is detected on both regular coefficients on the
reduced finite-type source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualRegularCoefficient_ext (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (a b : DualNumber Γ(X.left, ⊤))
    (h : ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) a =
        Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) b) : a = b := by
  apply TrivSqZeroExt.ext
  · apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_top_ext X
    intro p
    have hp := congrArg TrivSqZeroExt.fst (h p)
    change Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p a.fst = Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p b.fst at hp
    simpa only [Complex.TopSectionValues.complexSectionValue_top_formula, Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval] using hp
  · apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_top_ext X
    intro p
    have hp := congrArg TrivSqZeroExt.snd (h p)
    change Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p a.snd = Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p b.snd at hp
    simpa only [Complex.TopSectionValues.complexSectionValue_top_formula, Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval] using hp

theorem dualAffineSectionCoefficients_natural {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (f : X ⟶ Y) (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, ⊤)) :
    SectionCoefficients.dualAffineSectionCoefficients X ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appTop s) =
      Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom f) (SectionCoefficients.dualAffineSectionCoefficients Y s) := by
  apply dualRegularCoefficient_ext X
  intro p
  rw [← SectionCoefficients.dualAffineSectionCoefficients_evaluation, Dual.ConstantPointNaturality.dualConstantPoint_sectionValue_natural,
    SectionCoefficients.dualAffineSectionCoefficients_evaluation, Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_natural]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality
