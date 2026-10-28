import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePicardCoefficients

/-! # Picard Coefficient Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PicardCoefficientTransport.Construction

noncomputable section

/-! Coefficient transport from affine dual numbers to native reduced-open sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] AffinePicardCoefficients.Construction.affinePicardDualIsAffine

private theorem coefficient_transport_eq
    {B A C : Type} [CommRing B] [CommRing A] [CommRing C]
    (e : B ≃+* A) (t : C ≃+* A) (y : DualNumber C) (x : DualNumber B) (c : B)
    (hy : y = AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (t.symm.toRingHom.comp e.toRingHom) x)
    (hx : x.snd = c) : t y.snd = e c := by
  rw [hy]
  change t (t.symm (e x.snd)) = e c
  rw [RingEquiv.apply_symm_apply, hx]

private theorem nativeReducedOpen_coefficient_transport
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ)
    (a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion a.left]
    (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens)
    (hR : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U = a.left.opensRange)
    (y : DualNumber Γ(G.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U))
    (z : DualNumber B) (c : B)
    (h : y = AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap ((AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm).toRingHom.comp
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a).toRingHom) z)
    (hz : z.snd = c) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR y.snd = AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a c := by
  rw [← Canonical.OpenSections.Construction.regularSectionTransport_reverse hR] at h
  exact coefficient_transport_eq (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a)
    (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR) y z c h hz

/-- Recover the native Picard coefficient from its affine dual-number coordinate. -/
theorem nativePicardCoefficient_from_coordinates
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ)
    (a : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion a.left]
    (u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange)ˣ)
    (c : B)
    (hn : (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
      (CommAlgCat.of ℂ (DualNumber B)) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G)
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a)).symm.toMonoidHom u).val.snd = c) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange
        (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left) u.val).snd =
      AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G a c := by
  exact nativeReducedOpen_coefficient_transport G B a
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B a).left.opensRange (AffinePicardCoefficients.Construction.dualAffineChart_reducedRange G B a)
    _ _ c (AffinePicardCoefficients.Construction.nativeAffineChart_dualOpen_coefficients G B a u.val) hn

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PicardCoefficientTransport.Construction
