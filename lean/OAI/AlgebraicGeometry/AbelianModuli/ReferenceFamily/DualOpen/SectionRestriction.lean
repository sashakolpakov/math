import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedOpenMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionNaturality

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionRestriction

noncomputable section

/-! The actual regular coefficient equivalences on affine family
opens commute with every restriction between those opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualOpenSectionCoefficientEquiv_restrict (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left]
    {U V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    SectionEquivalence.dualOpenSectionCoefficientEquiv X V hV ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map (homOfLE h).op s) =
      Dual.NumberCoefficients.dualNumberRingMap (X.left.presheaf.map
        (homOfLE ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h)).op).hom
        (SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s) := by
  let : IsAffine (Product.dualReducedOpenOver X U).left := Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  let : IsAffine (Product.dualReducedOpenOver X V).left := Dual.ReductionOpens.dualAffineOpen_reduction X V hV
  let : LocallyOfFiniteType (Product.dualReducedOpenOver X V).hom := by
    change LocallyOfFiniteType (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι ≫ X.hom)
    infer_instance
  let : IsReduced (Product.dualReducedOpenOver X V).left :=
    inferInstanceAs (IsReduced ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).toScheme)
  let hf := SectionEquivalence.dualOpenProductMap_lands X U
  let hg := SectionEquivalence.dualOpenProductMap_lands X V
  have hgf : (⊤ : (LieRanks.dualNumberTest ℂ ⊗ Product.dualReducedOpenOver X V).left.Opens) ≤
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (Dual.ReducedOpenMaps.dualReducedOpenMap X h ≫ Product.dualReducedOpenInclusion X U)).left ⁻¹ᵁ U := by
    rw [Dual.ReducedOpenMaps.dualReducedOpenMap_inclusion]
    exact hg.trans ((Product.dualOpenProductMap X V).preimage_mono h)
  have hn := CoefficientPullback.dualPulledSectionCoefficients_natural (Dual.ReducedOpenMaps.dualReducedOpenMap X h)
    (Product.dualReducedOpenInclusion X U) U hf hgf s
  have hr := CoefficientPullback.dualPulledSectionCoefficients_restrict (Product.dualReducedOpenInclusion X V) U V h hg s
  have hc := CoefficientPullback.dualPulledSectionCoefficients_congr
    (Dual.ReducedOpenMaps.dualReducedOpenMap X h ≫ Product.dualReducedOpenInclusion X U) (Product.dualReducedOpenInclusion X V)
    (Dual.ReducedOpenMaps.dualReducedOpenMap_inclusion X h) U hgf
    (hg.trans ((Product.dualOpenProductMap X V).preimage_mono h)) s
  have he := hr.trans (hc.symm.trans hn)
  rw [SectionEquivalence.dualOpenSectionCoefficientEquiv_apply, SectionEquivalence.dualOpenSectionCoefficientEquiv_apply]
  change Dual.NumberCoefficients.dualNumberRingMap ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom.hom
      (CoefficientPullback.dualPulledSectionCoefficients (Product.dualReducedOpenInclusion X V) V hg
        ((LieRanks.dualNumberTest ℂ ⊗ X).left.presheaf.map (homOfLE h).op s)) = _
  rw [he]
  apply TrivSqZeroExt.ext
  · change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom
        ((Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom (Dual.ReducedOpenMaps.dualReducedOpenMap X h)) _ ) = _
    rw [Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_apply]
    exact Open.TopSectionNaturality.openTopSection_restrict ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h) _
  · change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).topIso.hom
        ((Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom (Dual.ReducedOpenMaps.dualReducedOpenMap X h)) _ ) = _
    rw [Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_apply]
    exact Open.TopSectionNaturality.openTopSection_restrict ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.SectionRestriction
