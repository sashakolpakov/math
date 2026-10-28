import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.SectionCoefficients

/-! # Canonical Dual Chart Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualChartCoefficients

noncomputable section

/-! On the canonical affine presentation, the actual coefficient
chart used for translation recovers exactly the original dual-section
coefficient equivalence used in the Picard Cech construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem specMap_section_coefficients {R S : CommRingCat.{0}} {Y : Scheme.{0}}
    (φ : R ⟶ S) (f : Spec R ⟶ Y) (s : Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map φ ≫ f).appTop s) =
      φ ((Scheme.ΓSpecIso R).hom (f.appTop s)) := by
  rw [Scheme.Hom.comp_appTop]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) (f.appTop s)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

theorem dualAffineTranslationChart_canonical :
    (Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (CommAlgCat.of ℂ Γ(X.left, ⊤)) (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).left =
      Spec.map (CommRingCat.ofHom (Dual.NumberCoefficients.dualTensorCoefficients ℂ Γ(X.left, ⊤)).toRingHom) ≫
        RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X := by
  erw [Intrinsic.TranslationAffineChart.dualAffineTranslationChart_factor, Over.comp_left, Dual.CoefficientProductChart.dualCoefficientProductMap_left, Category.assoc]

theorem canonicalDualChart_sectionCoefficients (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    (Scheme.ΓSpecIso (.of (DualNumber Γ(X.left, ⊤)))).hom
      ((Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (CommAlgCat.of ℂ Γ(X.left, ⊤)) (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).left.appTop s) =
        DualAffine.SectionCoefficients.dualAffineSectionCoefficients X s := by
  have h := congrArg (fun f : Spec (.of (DualNumber Γ(X.left, ⊤))) ⟶
      (LieRanks.dualNumberTest ℂ ⊗ X).left => f.appTop s) (dualAffineTranslationChart_canonical X)
  have hspec := specMap_section_coefficients
    (R := CommRingCat.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))
    (S := CommRingCat.of (DualNumber Γ(X.left, ⊤)))
    (CommRingCat.ofHom (Dual.NumberCoefficients.dualTensorCoefficients ℂ Γ(X.left, ⊤)).toRingHom)
    (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X) s
  calc
    _ = (Scheme.ΓSpecIso (.of (DualNumber Γ(X.left, ⊤)))).hom
        ((Spec.map (CommRingCat.ofHom (Dual.NumberCoefficients.dualTensorCoefficients ℂ Γ(X.left, ⊤)).toRingHom) ≫
          RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).appTop s) :=
      congrArg (Scheme.ΓSpecIso (.of (DualNumber Γ(X.left, ⊤)))).hom h
    _ = Dual.NumberCoefficients.dualTensorCoefficients ℂ Γ(X.left, ⊤)
        ((Scheme.ΓSpecIso (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))).hom
          ((RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).appTop s)) := hspec
    _ = _ := (DualAffine.SectionCoefficients.dualAffineSectionCoefficients_apply X s).symm

theorem canonicalDualChart_unitCoefficients (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)ˣ) :
    Units.map (Scheme.ΓSpecIso (.of (DualNumber Γ(X.left, ⊤)))).hom.hom.toMonoidHom
      (Units.map
        (Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (CommAlgCat.of ℂ Γ(X.left, ⊤)) (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).left.appTop.hom.toMonoidHom u) =
      Units.map (DualAffine.SectionCoefficients.dualAffineSectionCoefficients X).toMonoidHom u :=
  Units.ext (canonicalDualChart_sectionCoefficients X u.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualChartCoefficients
