import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismOpenReductionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionSectionMorphism

/-! # Morphism Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.MorphismCoefficients

noncomputable section

/-! On compatible affine opens, original dual-family pullback acts
on both regular coefficients by the original reduced scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (f : X ⟶ Y) (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (h : V ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)

theorem dualOpenSectionCoefficientEquiv_morphism (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, U)) :
    SectionEquivalence.dualOpenSectionCoefficientEquiv X V hV ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U V h s) =
      Dual.NumberCoefficients.dualNumberRingMap (f.left.appLE ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ U)
        ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V) (Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_le f U V h)).hom
          (SectionEquivalence.dualOpenSectionCoefficientEquiv Y U hU s) := by
  let : IsAffine (Product.dualReducedOpenOver X V).left := Dual.ReductionOpens.dualAffineOpen_reduction X V hV
  let : IsAffine (Product.dualReducedOpenOver Y U).left := Dual.ReductionOpens.dualAffineOpen_reduction Y U hU
  let : LocallyOfFiniteType (Product.dualReducedOpenOver X V).hom := by
    change LocallyOfFiniteType (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι ≫ X.hom)
    infer_instance
  let : IsReduced (Product.dualReducedOpenOver X V).left :=
    inferInstanceAs (IsReduced ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).toScheme)
  let g := Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen f U V h
  have hcomp : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X V).left.Opens) ≤
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (g ≫ Product.dualReducedOpenInclusion Y U)).left ⁻¹ᵁ U := by
    rw [Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_inclusion]
    have hh := (SectionEquivalence.dualOpenProductMap_lands X V).trans ((Product.dualOpenProductMap X V).preimage_mono h)
    change (⊤ : (LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X V).left.Opens) ≤
      (Product.dualOpenProductMap X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left) ⁻¹ᵁ U at hh
    have he : Product.dualOpenProductMap X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left =
        (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (Product.dualReducedOpenInclusion X V ≫ f)).left := by
      change ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ Product.dualReducedOpenInclusion X V) ≫
        (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f)).left = _
      rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact he ▸ hh
  have hn := CoefficientPullback.dualPulledSectionCoefficients_natural g (Product.dualReducedOpenInclusion Y U) U
    (SectionEquivalence.dualOpenProductMap_lands Y U) hcomp s
  have hp : CoefficientPullback.dualPulledSectionCoefficients (Product.dualReducedOpenInclusion X V) V (SectionEquivalence.dualOpenProductMap_lands X V)
      ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U V h s) =
      CoefficientPullback.dualPulledSectionCoefficients (g ≫ Product.dualReducedOpenInclusion Y U) U hcomp s := by
    unfold CoefficientPullback.dualPulledSectionCoefficients
    apply congrArg (DualAffine.SectionCoefficients.dualAffineSectionCoefficients (Product.dualReducedOpenOver X V))
    have hs := Scheme.Hom.appLE_comp_appLE (Product.dualOpenProductMap X V)
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left U V ⊤ h (SectionEquivalence.dualOpenProductMap_lands X V)
    have he : Product.dualOpenProductMap X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left =
        (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (g ≫ Product.dualReducedOpenInclusion Y U)).left := by
      rw [Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_inclusion]
      change ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ Product.dualReducedOpenInclusion X V) ≫
        (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f)).left = _
      rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact (ConcreteCategory.congr_hom hs s).trans
      (ConcreteCategory.congr_hom (Open.ImmersionSectionMorphism.schemeAppLE_congrMap he U ⊤ _ hcomp) s)
  rw [SectionEquivalence.dualOpenSectionCoefficientEquiv_apply, SectionEquivalence.dualOpenSectionCoefficientEquiv_apply]
  change Dual.NumberCoefficients.dualNumberRingMap ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom.hom
    (CoefficientPullback.dualPulledSectionCoefficients (Product.dualReducedOpenInclusion X V) V (SectionEquivalence.dualOpenProductMap_lands X V)
      ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U V h s)) = _
  rw [hp, hn]
  apply TrivSqZeroExt.ext
  · change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom
      (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom g _) = _
    rw [Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_apply]
    exact Open.TopSectionMorphism.openTopSection_morphism f.left _ _ (Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_le f U V h) _
  · change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom
      (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom g _) = _
    rw [Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_apply]
    exact Open.TopSectionMorphism.openTopSection_morphism f.left _ _ (Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_le f U V h) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.MorphismCoefficients
