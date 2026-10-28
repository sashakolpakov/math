import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TwistingTransitionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism

/-! # Projective Twisting Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTwistingFrames

noncomputable section

/-! Actual frames and a sheaf isomorphism identify the pullback of the projective twisting line bundle with the line bundle supplying a projective map's generating sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) (m : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

def sectionQuotientTwistingFrames :
    CompatibleSheaf.CompatibleSheafFrames ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m) M where
  frame V i hi := LocalLinearFrames.sectionLocalFrameEquiv (s i.down) V
    (hi.trans (QuotientCoordinatePullback.sectionQuotient_coordinate_preimage f s hs I m hm i.down).le)
  restrict V W h i hi r :=
    (FrameCocycles.sectionNaturalFrames s).restrict V W h i.down
      (hi.trans (QuotientCoordinatePullback.sectionQuotient_coordinate_preimage f s hs I m hm i.down).le) r
  change V i j hi hj r := by
    have hsi := hi.trans (QuotientCoordinatePullback.sectionQuotient_coordinate_preimage f s hs I m hm i.down).le
    have hsj := hj.trans (QuotientCoordinatePullback.sectionQuotient_coordinate_preimage f s hs I m hm j.down).le
    have he : ((((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m).value V i j hi hj).val) =
        ((FrameCocycles.sectionFrameTransitions s).value V i.down j.down hsi hsj).val :=
      (TwistingTransitionValues.sectionQuotient_twistingTransition f s hs I m hm V i j hi hj hsi).trans
        (FrameCocycles.sectionFrameTransitions_value s V i.down j.down hsi hsj).symm
    exact (congrArg (fun a : Γ(X, V) => LocalLinearFrames.sectionLocalFrameEquiv (s i.down) V hsi (a * r)) he).trans
      ((FrameCocycles.sectionNaturalFrames s).compatible.change V i.down j.down hsi hsj r)

def sectionQuotientTwistingBundleIso : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).pullback m).sheaf ≅ M :=
  OpenFrame.PullbackIsomorphism.lineBundleFromOpenFrames_pullbackIso (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1) m (ProjectiveTwisting.Bundle.projectiveTwistingCover I) ≪≫
    Sheaf.FrameRecognition.openFrameSheafRecognitionIso ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).pullback m)
      (sectionQuotientTwistingFrames f s hs I m hm)
      (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover m (ProjectiveTwisting.Bundle.projectiveTwistingCover I))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTwistingFrames
