import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData

/-! # Embedding Bundle Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingBundleRecovery

noncomputable section

/-! Compatibility of actual projective embeddings recovers the defining
line bundle whenever both presentations are given by global sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
variable (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion i.left] [IsClosedImmersion j.left]
variable {L : Line.Bundles.LineBundle X.left} {M : Line.Bundles.LineBundle Y.left}
variable (D : (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X).SectionData L)
variable (E : (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y).SectionData M)
variable (f : X ⟶ Y) (h : f ≫ j = i)

def sectionEmbeddingCompatibleBundleIso : (M.pullback f.left).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullback f.left).mapIso E.twistingIso.symm ≪≫
    (Scheme.Modules.pullbackComp f.left j.left).app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
        (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf ≪≫ D.twistingIso

include i j D E h in
theorem sectionEmbeddingCompatibleBundle_class :
    Line.Bundles.LineBundle.pullbackClass f.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L :=
  Quotient.sound ⟨sectionEmbeddingCompatibleBundleIso i j D E f h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingBundleRecovery
