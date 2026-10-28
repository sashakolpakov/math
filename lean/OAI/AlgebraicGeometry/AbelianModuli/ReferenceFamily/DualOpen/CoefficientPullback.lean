import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.CoefficientNaturality
import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues

/-! # Coefficient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientPullback

noncomputable section

section

/-! A regular section on an actual open of a dual-number family has
regular coefficients after any affine pullback into that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]

def dualPulledSectionCoefficients (f : X ⟶ Y) (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (hf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U) :
    Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U) →+* DualNumber Γ(X.left, ⊤) :=
  (DualAffine.SectionCoefficients.dualAffineSectionCoefficients X).toRingHom.comp
    ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U ⊤ hf).hom

theorem dualPulledSectionCoefficients_evaluation (f : X ⟶ Y)
    (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (hf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U)) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) (dualPulledSectionCoefficients f U hf s) =
      RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues.dualOpenRegularFunctionValue Y U s (p ≫ f) := by
  exact (DualAffine.SectionCoefficients.dualAffineSectionCoefficients_evaluation X p
    ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U ⊤ hf s)).symm.trans
      (RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues.dualOpenRegularFunctionValue_pullback f U s hf p).symm

theorem dualPulledSectionCoefficients_natural {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left]
    [LocallyOfFiniteType T.hom] [IsReduced T.left] (g : T ⟶ X) (f : X ⟶ Y)
    (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (hf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)
    (hgf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ T).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (g ≫ f)).left ⁻¹ᵁ U)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U)) :
    dualPulledSectionCoefficients (g ≫ f) U hgf s =
      Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom g) (dualPulledSectionCoefficients f U hf s) := by
  apply DualAffine.CoefficientNaturality.dualRegularCoefficient_ext T
  intro p
  have h := dualPulledSectionCoefficients_evaluation f U hf s (p ≫ g)
  rw [Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_natural] at h
  change Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p)
      (Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom g) (dualPulledSectionCoefficients f U hf s)) = _ at h
  rw [dualPulledSectionCoefficients_evaluation, h, Category.assoc]

end

/-! The regular coefficient map respects restriction of the original
section to a smaller actual open of the dual-number family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualPulledSectionCoefficients_congr {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (f g : X ⟶ Y) (h : f = g) (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (hf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)
    (hg : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ g).left ⁻¹ᵁ U)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U)) :
    dualPulledSectionCoefficients f U hf s = dualPulledSectionCoefficients g U hg s := by
  subst g
  rfl

theorem dualPulledSectionCoefficients_restrict {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (f : X ⟶ Y) (U V : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) (h : V ≤ U)
    (hf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ V)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U)) :
    dualPulledSectionCoefficients f V hf
      ((LieRanks.dualNumberTest ℂ ⊗ Y).left.presheaf.map (homOfLE h).op s) =
    dualPulledSectionCoefficients f U
      (hf.trans ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.preimage_mono h)) s := by
  have e := (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.map_appLE hf (homOfLE h).op
  exact congrArg (fun q : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U) ⟶ Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤) =>
    DualAffine.SectionCoefficients.dualAffineSectionCoefficients X (q s)) e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientPullback
