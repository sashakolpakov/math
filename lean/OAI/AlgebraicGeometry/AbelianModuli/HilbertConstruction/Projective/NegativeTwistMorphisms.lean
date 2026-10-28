import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CompatibleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoefficientPairCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

/-! # Negative Twist Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistMorphisms

noncomputable section

/-! Every quasicoherent section on one projective coordinate chart is the image of its canonical negative-twist frame under an actual global module morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_quasicoherent_exists_negativeTwist_morphism
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent]
    (j : Fin (n + 1)) (s : Γ(M, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})) :
    ∃ (d : ℕ) (φ : (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf ⟶ M),
      φ.app (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})
        ((ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal).frame
          (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) (ULift.up j) le_rfl 1) = s := by
  obtain ⟨d, t, hself, ht⟩ := CompatibleSections.projective_quasicoherent_compatible_section_extension I M j s
  let T := ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d
  let a (i : ULift.{u} (Fin (n + 1))) := t i.down
  have ha : Sheaf.FrameCoefficientMaps.FrameMorphismCompatible (D := T.reciprocal) a := by
    apply Frame.CoefficientPairCompatibility.frameMorphismCompatible_reciprocal_of_pairwise T a
    intro i k
    change M.presheaf.map
      (homOfLE ((SectionCover.projectiveCoordinateSectionCover I).overlap_le_left i.down k.down)).op (t i.down) =
        (T.value ((SectionCover.projectiveCoordinateSectionCover I).overlap i.down k.down)
          i k inf_le_left inf_le_right).val • M.presheaf.map
            (homOfLE ((SectionCover.projectiveCoordinateSectionCover I).overlap_le_right i.down k.down)).op (t k.down)
    rw [show (T.value ((SectionCover.projectiveCoordinateSectionCover I).overlap i.down k.down)
      i k inf_le_left inf_le_right).val =
        ((SectionCover.projectiveCoordinateSectionCover I).transition i.down k.down) ^ d from
          Negative.ProjectiveTwistingBundle.projectiveTwistingTransition_coordinate I d i k]
    exact ht i.down k.down
  let E := ConstructedCompatibleFrames.openFrameSheafFrames T.reciprocal
  refine ⟨d, Sheaf.FrameCoefficientGluing.frameCoefficientMorphism E a ha (ProjectiveTwisting.Bundle.projectiveTwistingCover I), ?_⟩
  exact (Sheaf.FrameCoefficientGluing.frameCoefficientMorphism_frame E a ha (ProjectiveTwisting.Bundle.projectiveTwistingCover I) (ULift.up j)).trans hself

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistMorphisms
