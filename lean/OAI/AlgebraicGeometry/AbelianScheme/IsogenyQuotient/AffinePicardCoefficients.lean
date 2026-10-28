import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.OpenSections
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback

/-! # Affine Picard Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePicardCoefficients.Construction

noncomputable section

/-! The original Picard dual-open coefficients can be computed in any
actual affine presentation of the group open. The coordinate comparison
and the reduced-open transport are constructed from the scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance affinePicardDualIsAffine (B : CommAlgCat ℂ) :
    IsAffine (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B)).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (DualNumber B))))

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ)
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]

theorem dualAffineChart_reducedRange :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange =
      i.left.opensRange := by
  rw [AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range, AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover.dualProjectionReducedOpen]

private theorem coordinate_baseSection_transport
    (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B D : CommAlgCat ℂ)
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) (j : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (W : G.left.Opens) (hJ : j.left.opensRange = W) (hR : W = i.left.opensRange)
    (r : D → Γ(G.left, W))
    (hr : ∀ a, AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hJ
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ D G j a) = r a) (a : B) :
    r (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j (hJ.trans hR) a) =
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i a) := by
  have hs := congrArg (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hJ)
    (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap_sections G B D i j (hJ.trans hR) a)
  rw [hr] at hs
  rw [AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport_restrict hR.symm hJ (hJ.trans hR).le le_rfl] at hs
  have hid : G.left.presheaf.map (homOfLE (show W ≤ W from le_rfl)).op =
      𝟙 (G.left.presheaf.obj (.op W)) := G.left.presheaf.map_id (.op W)
  exact hs.trans (ConcreteCategory.congr_hom hid _)

private theorem nativeReducedOpen_baseSection
    (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens) (hU : IsAffineOpen U)
    (hR : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U = i.left.opensRange)
    (a : B) :
    let R := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U
    let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU
    let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU
    let hJ := Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU
    let h : j.left.opensRange = i.left.opensRange := hJ.trans hR
    let q := AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i
    R.topIso.hom (q a) = AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm (e a) := by
  let R := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U
  let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU
  let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU
  let hJ := Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU
  exact coordinate_baseSection_transport G B D i j R hJ hR R.topIso.hom
    (Canonical.OpenSections.Construction.nativeReducedOpenPresentation_sections G U hU) a

private theorem nativeAffineChart_coefficients_via_map
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange)) :
    let U := (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
    let hU := isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left
    let R := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U
    let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU
    let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU
    let hJ := Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU
    let hR := dualAffineChart_reducedRange G B i
    let h : j.left.opensRange = i.left.opensRange := hJ.trans hR
    let q := AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
    let eB := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)
    AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G U hU s =
      AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap R.topIso.hom.hom (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q (eB.symm s)) := by
  let U := (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
  let hU := isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left
  let R := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U
  let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU
  let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU
  let hJ := Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU
  let hR := dualAffineChart_reducedRange G B i
  have h : j.left.opensRange = i.left.opensRange := hJ.trans hR
  let q := AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
  let eB := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)
  let eD := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)
  have hc := Intrinsic.AffineCechComparison.Construction.nativeAffinePresentation_dualOpen_coefficients G U hU s
  have hn := Intrinsic.FrameCoordinateChange.Construction.sameOpenDualCoordinateMap_inverse G B D i j h s
  let hD := DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h
  let hC := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenTranslationChart_range G U hU
  have hr : AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hC.symm s =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.presheaf.map (homOfLE hD.le).op s := by
    rw [AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback.regularSectionTransport_eq_map]
    exact congrArg (fun f => (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.presheaf.map f s)
      (Subsingleton.elim _ _)
  change AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap R.topIso.hom.hom (eD.symm (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hC.symm s)) =
    AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G U hU s at hc
  rw [hr, ← hn] at hc
  exact hc.symm

private theorem nativeReducedOpen_coordinateMap_comp
    (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens) (hU : IsAffineOpen U)
    (hR : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U = i.left.opensRange)
    (z : DualNumber B) :
    let R := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U
    let D := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU
    let j := Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU
    let hJ := Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU
    let h : j.left.opensRange = i.left.opensRange := hJ.trans hR
    let q := AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i
    AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap R.topIso.hom.hom (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap q z) =
      AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap ((AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm).toRingHom.comp e.toRingHom) z := by
  dsimp only
  apply TrivSqZeroExt.ext
  · exact nativeReducedOpen_baseSection G B i U hU hR z.fst
  · exact nativeReducedOpen_baseSection G B i U hU hR z.snd

private theorem nativeReducedOpen_coefficients_compare
    (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens) (hU : IsAffineOpen U)
    (hR : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U = i.left.opensRange)
    (y : DualNumber Γ(G.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U))
    (z : DualNumber B)
    (h : y = AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ⁻¹ᵁ U).topIso.hom.hom
      (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B (Intrinsic.AffineCechComparison.Construction.nativeReducedOpenCoefficients G U hU)
        i (Intrinsic.AffineCechComparison.Construction.nativeReducedOpenPresentation G U hU)
        ((Canonical.OpenSections.Construction.nativeReducedOpenPresentation_range G U hU).trans hR)) z)) :
    y = AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap ((AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hR.symm).toRingHom.comp
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toRingHom) z :=
  h.trans (nativeReducedOpen_coordinateMap_comp G B i U hU hR z)

/-- Both coefficients in the original Picard construction are the
original affine coefficients, transported to the actual reduced open. -/
theorem nativeAffineChart_dualOpen_coefficients
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange)) :
    AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left) s =
      AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap
        ((AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (dualAffineChart_reducedRange G B i).symm).toRingHom.comp
          (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toRingHom)
        ((AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
          (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm s) := by
  exact nativeReducedOpen_coefficients_compare G B i
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
    (isAffineOpen_opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left)
    (dualAffineChart_reducedRange G B i) _ _
    (nativeAffineChart_coefficients_via_map G B i s)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePicardCoefficients.Construction
