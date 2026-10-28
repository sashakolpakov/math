import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.AffineCechComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IsoSpecSections

/-! # Open Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.OpenSections.Construction

noncomputable section

/-! The canonical presentation of the actual reduced open uses its
original regular sections. Its range and section identification are
derived from the native affine isomorphism and open inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IsoSpecSections

theorem regularSectionTransport_reverse {X : Scheme.{0}} {U V : X.Opens} (h : U = V) :
    (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport h).symm = AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport h.symm := by
  subst V
  rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U)

theorem nativeReducedOpenPresentation_range :
    (Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation X U hU).left.opensRange =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  have : IsIso (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv.left :=
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map_isIso (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv
  change ((Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv.left ≫
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

theorem nativeReducedOpenPresentation_sections (a : Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤)) :
    AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (nativeReducedOpenPresentation_range X U hU)
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ
        (Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients X U hU) X
        (Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation X U hU) a) =
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom a := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  let W := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U
  let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients X U hU
  let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation X U hU
  let k : (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D).left ⟶ W.toScheme :=
    (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv.left
  let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ D X j
  let hR := nativeReducedOpenPresentation_range X U hU
  have hp : k ≫ W.ι = j.left := rfl
  have hf : (⊤ : (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D).left.Opens) ≤ j.left ⁻¹ᵁ W := by
    change ⊤ ≤ j.left ⁻¹ᵁ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U)
    rw [← hR, j.left.preimage_opensRange]
  have hj : (⊤ : (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D).left.Opens) ≤ j.left ⁻¹ᵁ j.left.opensRange := by
    rw [j.left.preimage_opensRange]
  have hΓ : k.appTop = (Scheme.ΓSpecIso (.of D)).inv :=
    AbelianModuli.ReferenceFamily.Affine.IsoSpecSections.affineIsoSpec_inv_appTop (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left
  have htransport := AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism.regularSectionTransport_appLE j.left hR.symm rfl hf hj (W.topIso.hom a)
  have hlift := AbelianModuli.ReferenceFamily.Open.LiftSectionMap.openLift_sectionMap W k j.left hp hf (W.topIso.hom a)
  have hcoeff : e.symm (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm (W.topIso.hom a)) = a := by
    rw [Intrinsic.AffineCechComparison.Construction.affinePresentation_inverse_section]
    calc
      (Scheme.ΓSpecIso (.of D)).hom
          (j.left.appLE j.left.opensRange ⊤ hj
            (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm (W.topIso.hom a))) =
          (Scheme.ΓSpecIso (.of D)).hom (k.appTop (W.topIso.inv (W.topIso.hom a))) :=
        congrArg (Scheme.ΓSpecIso (.of D)).hom (htransport.symm.trans hlift.symm)
      _ = a := by
        rw [W.topIso.hom_inv_id_apply, hΓ]
        exact (Scheme.ΓSpecIso (.of D)).inv_hom_id_apply a
  have he := congrArg e hcoeff
  rw [RingEquiv.apply_symm_apply] at he
  have ht := congrArg (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR) he
  rw [← regularSectionTransport_reverse hR, RingEquiv.apply_symm_apply] at ht
  exact ht.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.OpenSections.Construction
