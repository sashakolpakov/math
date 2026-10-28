import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PullbackFiniteDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Morphism Ample Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismAmpleDescent

noncomputable section

/-! A generating section morphism is finite if its line bundle becomes ample after a surjective base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) [IsProper f] (g : Y ⟶ S) [Surjective g]
variable (L : Line.Bundles.LineBundle X) {n : ℕ} (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (hL : (L.pullback (pullback.fst f g)).IsAmple)

include hL

theorem sectionProjectiveMorphism_isFinite_of_ample_surjective_baseChange :
    IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := by
  let q := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  have : IsProper (q.left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom) := q.w.symm ▸ inferInstanceAs (IsProper f)
  have : IsProper q.left := IsProper.of_comp q.left (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
  have : Surjective (pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom g).flip
      (inferInstance : Surjective g)
  apply Ample.PullbackFiniteDescent.proper_isFinite_of_ample_pullback_after_surjective_baseChange
    (Projective.PresentationBaseChange.overPullback_map_isPullback q g) (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n)
  exact hL.of_iso ((Scheme.Modules.pullback (pullback.fst f g)).mapIso
    (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs).symm)

theorem sectionAbsoluteMorphism_isFinite_of_ample_surjective_baseChange [IsAffine S] :
    IsFinite (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  let q := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  let p := pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hq : IsFinite q.left := sectionProjectiveMorphism_isFinite_of_ample_surjective_baseChange f g L s hs hL
  have : IsIso p := inferInstanceAs
    (IsIso (pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  have hp : IsFinite p := inferInstance
  have h : IsFinite (q.left ≫ p) := MorphismProperty.comp_mem (@IsFinite) _ _ hq hp
  have he : q.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := pullback.lift_fst _ _ _
  exact he ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismAmpleDescent
