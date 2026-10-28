import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SuboverlapTransitions
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionInclusions

/-! # Intersection Maps -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionMaps.Dolbeault

noncomputable section

/-! Restriction between original projective Čech intersections, in the chosen
frames, is ordinary function restriction times the normalized transition power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistIntersectionFunction (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) :=
  Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) i
    (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d a

def projectiveTwistIntersectionFunctionEquiv (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) ≃+
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) :=
  (Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n
    (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) i (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d)).toAddEquiv

theorem projectiveTwistIntersectionFunctionEquiv_apply (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))) :
    projectiveTwistIntersectionFunctionEquiv n s i hi j d a =
      projectiveTwistIntersectionFunction n s i hi j d a := rfl

theorem projectiveTwistIntersectionFunction_restrict (n : ℕ)
    {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i : Fin (n + 1)) (hi : i ∈ t) (k : Fin (n + 1)) (hk : k ∈ s)
    (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s))))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n t)) :
    projectiveTwistIntersectionFunction n t i hi j d
        ((Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono
          (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst))).op a) p =
      projectiveTwistIntersectionFunction n s k hk j d a
        ⟨p.val, Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (Projective.IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst) p.property⟩ *
        (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d := by
  have ht := SuboverlapTransitions.Dolbeault.projectiveTwistOpenSectionFunction_suboverlap n i k j d (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n t)
    (Projective.IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_le_overlap n t i hi k (hst hk))
    ((Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono
      (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst))).op a) p
  have hr := FrameRestriction.Dolbeault.projectiveTwistOpenSectionFunction_restrict n (Projective.IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst)
    k (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s k hk) j d a p
  exact ht.trans (congrArg (fun z : ℂ => z *
    (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d) hr)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionMaps.Dolbeault
