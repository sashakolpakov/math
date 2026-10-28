import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration

/-! # Section Embedded Variety -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionEmbeddedVariety

noncomputable section

/-! For an actual section embedding the Fubini–Study class is the
original Chern class of its line bundle on the original complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {M : V.toOver.left.Modules} {n : ℕ}
  (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.toOver.left ⟶ M))
  (hs : ∀ x : V.toOver.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
  (hc : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism V.toOver.hom s hs))

def sectionEmbeddedVariety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.ofClosedImmersion V.toOver.hom n (Intrinsic.SectionMorphism.nativeSectionMorphism V.toOver s hs).left
    (Intrinsic.SectionMorphism.nativeSectionMorphism_closedImmersion V.toOver s hs hc) (Intrinsic.SectionMorphism.nativeSectionMorphism V.toOver s hs).w
    V.presentation.smooth V.property

theorem sectionEmbeddedVariety_coordinates :
    ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates (sectionEmbeddedVariety V s hs hc) =
      Intrinsic.SectionCoordinates.nativeSectionCoordinates V.toOver s hs := rfl

theorem sectionEmbeddedVariety_chern (L : HilbertConstruction.Line.Bundles.LineBundle V.toOver.left)
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.toOver.left ⟶ L.sheaf))
    (hs : ∀ x : V.toOver.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (hc : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism V.toOver.hom s hs)) :
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ (sectionEmbeddedVariety V s hs hc) = Intrinsic.ChernClasses.lineBundleChernClass V.presentation L := by
  let W := sectionEmbeddedVariety V s hs hc
  have h := SectionChernComparison.lineBundleChernClass_sectionMorphism W L s hs
  exact h.symm.trans (ChernEmbeddingIndependence.lineBundleChernClass_changeEmbedding V.presentation W.presentation.projective L)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionEmbeddedVariety
