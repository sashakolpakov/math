import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualOpenChartCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

/-! # Affine Cech Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.AffineCechComparison.Construction

noncomputable section

/-! The original affine-presentation coefficients and the original
dual-open Picard coefficients agree on the constructed canonical
presentation. All open ranges and commuting maps are proved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

theorem affinePresentation_inverse_section
    (k : Type) [CommRing k] (B : CommAlgCat k) (X : Over (Spec (.of k)))
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ X) [IsOpenImmersion i.left]
    (s : Γ(X.left, i.left.opensRange)) :
    (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv k B X i).symm s =
      (Scheme.ΓSpecIso (.of B)).hom
        (i.left.appLE i.left.opensRange ⊤ (by rw [i.left.preimage_opensRange]) s) := by
  change (Scheme.ΓSpecIso (.of B)).hom ((IsOpenImmersion.ΓIsoTop i.left).inv s) = _
  rw [AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections.openImmersionTopSectionIso_inv]

theorem dualAffineTranslationChart_postcompose
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (B : CommAlgCat ℂ) (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) (f : X ⟶ Y) :
    AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart Y B (i ≫ f) =
      AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X B i ≫ (𝟙 (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f) := by
  simp only [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_factor, Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp]

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U)

def nativeReducedOpenCoefficients : CommAlgCat ℂ := by
  letI : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  exact CommAlgCat.of ℂ Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤)

def nativeReducedOpenPresentation :
    AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ (nativeReducedOpenCoefficients X U hU) ⟶ X := by
  letI : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  exact (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv ≫ AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenInclusion X U

instance nativeReducedOpenPresentation_open :
    IsOpenImmersion (nativeReducedOpenPresentation X U hU).left := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  change IsOpenImmersion ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv.left ≫
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι)
  infer_instance

theorem nativeDualOpenCoefficientChart_ambient :
    DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU ≫ U.ι =
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (nativeReducedOpenCoefficients X U hU)
        (nativeReducedOpenPresentation X U hU)).left := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  rw [DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart_inclusion, nativeReducedOpenPresentation,
    dualAffineTranslationChart_postcompose]
  rfl

instance nativeDualOpenCoefficientChart_isIso : IsIso (DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU) := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  let Y := AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U
  have ht : IsIso (𝟙 (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).inv).left :=
    inferInstanceAs (IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map
      (𝟙 (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).inv)))
  erw [DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart, AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_factor, Over.comp_left]
  infer_instance

theorem nativeReducedOpenTranslationChart_range :
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (nativeReducedOpenCoefficients X U hU)
      (nativeReducedOpenPresentation X U hU)).left.opensRange = U := by
  apply TopologicalSpace.Opens.ext
  change Set.range (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (nativeReducedOpenCoefficients X U hU)
    (nativeReducedOpenPresentation X U hU)).left = (U : Set (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left)
  rw [← nativeDualOpenCoefficientChart_ambient]
  change Set.range (U.ι ∘ DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU) = _
  have hs : Function.Surjective (DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU) :=
    (inferInstance : Surjective (DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU)).surj
  rw [Set.range_comp, hs.range_eq, Set.image_univ]
  exact congrArg SetLike.coe (Scheme.Opens.opensRange_ι U)

/-- On the constructed native affine presentation, both regular
coefficients equal the original dual-open coefficients, with the literal
open-range transport. -/
theorem nativeAffinePresentation_dualOpen_coefficients
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (R := Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))
      (S := Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U))
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom.hom
      ((AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
        (CommAlgCat.of ℂ (DualNumber (nativeReducedOpenCoefficients X U hU)))
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X)
        (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X (nativeReducedOpenCoefficients X U hU)
          (nativeReducedOpenPresentation X U hU))).symm
        (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (nativeReducedOpenTranslationChart_range X U hU).symm s)) =
      AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s := by
  let B := nativeReducedOpenCoefficients X U hU
  let j := AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart X B (nativeReducedOpenPresentation X U hU)
  let p := DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X U hU
  have hp : p ≫ U.ι = j.left := nativeDualOpenCoefficientChart_ambient X U hU
  have hf : (⊤ : (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B)).left.Opens) ≤ j.left ⁻¹ᵁ U := by
    intro x _
    have hx := congrArg (fun f => f x) hp
    change j.left x ∈ U
    exact hx ▸ (p x).property
  have hj : (⊤ : (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B)).left.Opens) ≤ j.left ⁻¹ᵁ j.left.opensRange := by
    rw [j.left.preimage_opensRange]
  have htransport := AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism.regularSectionTransport_appLE j.left
    (nativeReducedOpenTranslationChart_range X U hU).symm rfl hf hj s
  have hlift := AbelianModuli.ReferenceFamily.Open.LiftSectionMap.openLift_sectionMap U p j.left hp hf s
  have he : (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X) j).symm
      (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (nativeReducedOpenTranslationChart_range X U hU).symm s) =
      (Scheme.ΓSpecIso (.of (DualNumber B))).hom (p.appTop (U.topIso.inv s)) := by
    rw [affinePresentation_inverse_section]
    exact congrArg (Scheme.ΓSpecIso (.of (DualNumber B))).hom
      (htransport.symm.trans hlift.symm)
  change AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap _
    ((AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X) j).symm _) = _
  rw [he]
  exact DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart_coefficients X U hU s

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.AffineCechComparison.Construction
