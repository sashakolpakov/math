import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionMaps

/-! # Frame Domain Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameDomainTransport.Dolbeault

noncomputable section

/-! The two existing projective intersection frames agree under original open transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistIntersectionFrame_transport (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    ProjectiveTwist.IntersectionFrames.Dolbeault.projectiveAnalytifiedTwist_intersectionUnitIso n s i hi j d =
      Open.UnitFrame.Dolbeault.transportOpenUnitFrame (M := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d) (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s)
        (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)
          i (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d) := by
  have h : HEq (ProjectiveTwist.IntersectionFrames.Dolbeault.projectiveAnalytifiedTwist_intersectionUnitIso n s i hi j d)
      (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)
        i (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d) := by
    unfold ProjectiveTwist.IntersectionFrames.Dolbeault.projectiveAnalytifiedTwist_intersectionUnitIso
    exact cast_heq _ _
  exact eq_of_heq (h.trans (Open.UnitFrame.Dolbeault.transportOpenUnitFrame_heq
    (M := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
    (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d) (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s)
    (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)
      i (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d)).symm)

theorem projectiveTwistSectionFrame_domain_transport (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))) :
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.map
      (homOfLE (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).ge).op
      (ProjectiveTwist.SectionCoordinates.Dolbeault.projectiveTwistSectionFrame n s i hi j d a) =
      ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s i hi j d
        ((ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map
          (homOfLE (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).ge).op a) := by
  have h := Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv_domain_transport (M := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
    (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d) (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s)
    (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)
      i (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d) a
  rw [← projectiveTwistIntersectionFrame_transport] at h
  exact h

theorem projectiveTwistSectionFrame_point_transport (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (p : IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) :
    (show DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) from ProjectiveTwist.SectionCoordinates.Dolbeault.projectiveTwistSectionFrame n s i hi j d a).val p =
      ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s i hi j d
        ((ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map
          (homOfLE (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).ge).op a)
        ⟨p.val, (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).le p.property⟩ := by
  exact congrArg (fun f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction
      (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) =>
        f ⟨p.val, (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).le p.property⟩)
    (projectiveTwistSectionFrame_domain_transport n s i hi j d a)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameDomainTransport.Dolbeault
