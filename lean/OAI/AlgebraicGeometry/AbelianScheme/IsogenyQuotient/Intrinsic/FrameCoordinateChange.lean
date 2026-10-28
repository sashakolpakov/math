import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualAffineCoordinateNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Frame Coordinate Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCoordinateChange.Construction

noncomputable section

/-! Native frame coefficients transform by the constructed original
coordinate map. This follows from the actual dual affine scheme square,
including the original open restrictions and transition sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B D : CommAlgCat ℂ)
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) (j : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (h : j.left.opensRange = i.left.opensRange)

theorem sameOpenDualCoordinateMap_inverse
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange)) :
    AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberAlgMap (AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h)
      ((AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm s) =
      (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)).symm
        ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.presheaf.map
          (homOfLE (DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h).le).op s) := by
  apply (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)).injective
  rw [DualAffineCoordinateNaturality.Construction.sameOpenDualCoordinateMap_sections, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem sameOpenDualCoordinateMap_unitCoefficient
    (u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange)ˣ) :
    (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)).symm.toMonoidHom
      (Units.map ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.presheaf.map
        (homOfLE (DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h).le).op).hom.toMonoidHom u)).val.snd =
      AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
        (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
          (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom u).val.snd :=
  (congrArg TrivSqZeroExt.snd (sameOpenDualCoordinateMap_inverse G B D i j h u.val)).symm

theorem nativeFrameCoefficient_coordinateChange
    {M : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Modules} (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M)
    (hs : (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange ≤ s.domain)
    (ht : (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange ≤ t.domain) :
    (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber D))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j)).symm.toMonoidHom
      (s.transition t (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G D j).left.opensRange
        ((DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h).le.trans hs)
        ((DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h).le.trans ht))).val.snd =
      AffinePresentationChange.Construction.sameOpenAffineCoordinateMap G B D i j h
        (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
          (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom
          (s.transition t (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange hs ht)).val.snd := by
  rw [← AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame.transition_restrict s t (DualAffineCoordinateNaturality.Construction.sameOpenDualChart_range G B D i j h).le hs ht]
  exact sameOpenDualCoordinateMap_unitCoefficient G B D i j h _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCoordinateChange.Construction
