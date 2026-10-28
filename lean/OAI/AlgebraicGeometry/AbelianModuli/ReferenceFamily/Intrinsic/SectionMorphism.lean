import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleSectionEmbedding

/-! # Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionMorphism

noncomputable section

/-! Section embeddings into the original native complex projective
space, with their actual local coordinate formulas retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {L : X.left.Modules} {n : ℕ}
  (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L))
  (hs : ∀ x : X.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))

def nativeSectionMorphism : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  Over.homMk ((HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left ≫ (ProjectiveAdapter.ProjectiveCoefficients.complexProjectiveIso n).hom)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left ≫ a)
        (ProjectiveAdapter.ProjectiveCoefficients.complexProjectiveIso_base n)).trans (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).w))

theorem nativeSectionMorphism_left :
    (nativeSectionMorphism X s hs).left = HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs ≫
      ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n := by
  change (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left ≫
    (pullback.fst (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) n).hom Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ ≫
      ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n)
      (pullback.lift_fst _ _ _))

theorem nativeSectionMorphism_restrict (i : Fin (n + 1)) :
    (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ (nativeSectionMorphism X s hs).left =
      HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap
        ((((HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ X.hom).appTop.hom).comp
          ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom)
        (fun j => HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) i (HilbertConstruction.Section.Frames.sectionRatio_self (s i)) := by
  exact (congrArg (fun a => (HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ a)
    (nativeSectionMorphism_left X s hs)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n)
        (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict X.hom s hs i)).trans
        (ProjectiveChartCoefficients.ProjectiveCoefficients.projectiveChartMap_coefficients ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom
          ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ X.hom).appTop.hom
          (fun j => HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) i (HilbertConstruction.Section.Frames.sectionRatio_self (s i)))))

theorem nativeSectionMorphism_closedImmersion
    (hc : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs)) :
    IsClosedImmersion (nativeSectionMorphism X s hs).left := by
  have : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs) := hc
  have : IsIso (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n) :=
    inferInstanceAs (IsIso (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeIso ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv n).inv)
  have h : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs ≫
      ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom n) := inferInstance
  exact (nativeSectionMorphism_left X s hs).symm ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionMorphism
