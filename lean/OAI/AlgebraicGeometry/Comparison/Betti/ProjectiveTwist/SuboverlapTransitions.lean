import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions

/-! # Suboverlap Transitions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SuboverlapTransitions.Dolbeault

noncomputable section

/-! The normalized transition formula holds on every smaller algebraic open
inside a coordinate overlap, including all finite Čech intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAlgebraicTwistOpenFrame_suboverlap_transition (n : ℕ)
    (i k j : Fin (n + 1)) (d : ℤ) (V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (hV : V ≤ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n V i
        (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k)) j d).hom =
      (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n V k
        (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)) j d).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf V
          ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE hV).op (FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d)) := by
  have h := SheafCohomology.Projective.OverFrameTransitions.restrictOverTrivialization_hom_eq_comp_scalar
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) hV
    (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k) j d)
    (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k) j d)
    (FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d) (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame_transition n i k j d)
  rw [FrameRestriction.Dolbeault.projectiveAlgebraicTwistOpenFrame_restrict, FrameRestriction.Dolbeault.projectiveAlgebraicTwistOpenFrame_restrict] at h
  exact h

theorem projectiveTwistOpenSectionFunction_suboverlap (n : ℕ)
    (i k j : Fin (n + 1)) (d : ℤ) (V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (hV : V ≤ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) V)))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) V) :
    Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V i
        (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k)) j d a p =
      Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V k
        (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)) j d a p *
        (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have h := Holomorphic.FrameScalars.holomorphicAnalytificationFrameSection_scalar X V
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) _ _ _
    (projectiveAlgebraicTwistOpenFrame_suboverlap_transition n i k j d V hV) a
  have hp := congrArg (fun f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel X) (M := Open.AffineIsoEvaluation.analyticOpen X V) =>
    f.val p) h
  change Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V i
      (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k)) j d a p =
    Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V k
      (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)) j d a p *
      Holomorphic.RegularSections.regularHolomorphicSectionMap X V ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE hV).op
        (FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d)) p at hp
  have hs : Holomorphic.RegularSections.regularHolomorphicSectionMap X V ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE hV).op
      (FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d)) p =
      (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d :=
    (Open.AffineIsoEvaluation.sectionEvaluationOn_restrict X hV (FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d) p).trans
      (Projective.TransitionEvaluation.Dolbeault.projectiveTwistTransitionSection_evaluation n i k d _)
  exact hp.trans (congrArg (fun z : ℂ => Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V k
    (hV.trans (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)) j d a p * z) hs)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SuboverlapTransitions.Dolbeault
