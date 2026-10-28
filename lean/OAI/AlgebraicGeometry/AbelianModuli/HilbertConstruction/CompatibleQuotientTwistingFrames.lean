import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientCoordinatePullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistPullbackValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

/-! # Compatible Quotient Twisting Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientTwistingFrames

noncomputable section

/-! The actual degree-one twisting bundles are compatible with morphisms of homogeneous projective quotients over the same ambient projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable (m : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)

theorem projectiveTwistingTransition_one (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (i j : ULift.{u} (Fin (n + 1)))
    (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}) (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down}) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).value V i j hi hj).val =
      ProjectiveFrame.Ratios.projectiveFrameRatio I V i.down j.down hi hj := pow_one _

include hm in
theorem compatibleQuotient_twistingTransition (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (i j : ULift.{u} (Fin (n + 1)))
    (hi : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i.down})
    (hj : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {j.down})
    (hi' : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down})
    (hj' : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j.down}) :
    ((((ProjectiveTwisting.Bundle.projectiveTwistingTransitions J 1).pullback m).value V i j hi hj).val) =
      ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1).value V i j hi' hj').val :=
  (Projective.TwistPullbackValues.projectiveTwistingPullback_singleton J m V i j hi hj).trans
    ((CompatibleQuotientCoordinatePullbacks.compatibleQuotient_coordinate_pullback I J m hm i.down j.down V hi hi').trans
      ((Quotient.CoordinatePullback.projectiveFrameRatio_from_singleton I V i.down j.down hi' hj').symm.trans
        (projectiveTwistingTransition_one I V i j hi' hj').symm))

def compatibleQuotientTwistingFrames : CompatibleSheaf.CompatibleSheafFrames ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions J 1).pullback m)
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf where
  frame V i hi := (ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)).frame V i
    (hi.trans (CompatibleQuotientCoordinatePullbacks.compatibleQuotient_coordinate_preimage I J m hm i.down).le)
  restrict V W h i hi r := (ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)).restrict V W h i
    (hi.trans (CompatibleQuotientCoordinatePullbacks.compatibleQuotient_coordinate_preimage I J m hm i.down).le) r
  change V i j hi hj r := by
    have hi' := hi.trans (CompatibleQuotientCoordinatePullbacks.compatibleQuotient_coordinate_preimage I J m hm i.down).le
    have hj' := hj.trans (CompatibleQuotientCoordinatePullbacks.compatibleQuotient_coordinate_preimage I J m hm j.down).le
    let E := ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
    have he := compatibleQuotient_twistingTransition I J m hm V i j hi hj hi' hj'
    exact (congrArg (fun a => E.frame V i hi' (a * r)) he).trans (E.change V i j hi' hj' r)

def compatibleQuotientTwistingBundleIso :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle J 1).pullback m).sheaf ≅ (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf :=
  OpenFrame.PullbackIsomorphism.lineBundleFromOpenFrames_pullbackIso (ProjectiveTwisting.Bundle.projectiveTwistingTransitions J 1) m (ProjectiveTwisting.Bundle.projectiveTwistingCover J) ≪≫
    Sheaf.FrameRecognition.openFrameSheafRecognitionIso ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions J 1).pullback m)
      (compatibleQuotientTwistingFrames I J m hm)
      (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover m (ProjectiveTwisting.Bundle.projectiveTwistingCover J))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientTwistingFrames
