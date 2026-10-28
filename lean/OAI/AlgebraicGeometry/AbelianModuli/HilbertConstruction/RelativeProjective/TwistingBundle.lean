import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Twisting Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The relative projective twisting bundle pulls back along the constructed projective embeddings to the actual positive power used to define them. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (S : Scheme.{u}) (n : ℕ) : Line.Bundles.LineBundle (Projective.ProjectivePresentations.projectiveSpaceOver S n).left :=
  (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) n).pullback
    (Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ)

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)

def RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left).sheaf ≅ M := by
  let L := Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) n
  let p := Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs :=
    Limits.pullback.lift_fst _ _ _
  exact (Scheme.Modules.pullbackComp (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left p).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr hp).app L.sheaf ≪≫ Section.AbsoluteTwistingBundle.sectionAbsoluteTwistingBundleIso f s hs

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.twistingBundleIso {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension).pullback
      (SectionsProjectiveMorphism.sectionProjectiveMorphism f E.sections E.covers).left).sheaf ≅ E.power.sheaf :=
  RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f E.sections E.covers

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.twistingBundle_isTensorPower {L : Line.Bundles.LineBundle X}
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f) :
    Tensor.Powers.IsTensorPower L.sheaf E.degree
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension).pullback
        (SectionsProjectiveMorphism.sectionProjectiveMorphism f E.sections E.covers).left).sheaf :=
  E.isPower.of_targetIso (E.twistingBundleIso f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
