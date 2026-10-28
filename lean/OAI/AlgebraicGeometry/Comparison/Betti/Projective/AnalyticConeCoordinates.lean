import OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameDomainTransport
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Cone
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.AcyclicCover

/-! # Analytic Cone Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.AnalyticConeCoordinates.Dolbeault

noncomputable section

/-! Cone coordinates on the actual analytic-open presentation used by the Cech maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveIntersectionOpenSectionIso (n : ℕ) (s : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (d : ℤ) :
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj (op (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) ≅
      (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
        (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) :=
  (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.mapIso
    (eqToIso (congrArg op (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s)))

theorem projectiveIntersectionOpenSectionIso_hom (n : ℕ) (s : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))) :
    (projectiveIntersectionOpenSectionIso n s j d).hom a =
      (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map
        (homOfLE (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).ge).op a := by
  change (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _ a =
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _ a
  exact congrArg (fun u : op (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) ⟶
      op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) =>
        (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map u a) (Subsingleton.elim _ _)

def projectiveTwistAnalyticConeCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) ≃+
        HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d :=
  (projectiveIntersectionOpenSectionIso n s j d).symm.addCommGroupIsoToAddEquiv.trans
    (ProjectiveTwist.Cone.Dolbeault.projectiveTwistConeCoordinates n s i hi j d)

def projectiveAnalyticConePoint (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s) :=
  ⟨(ProjectiveTwist.Cone.Dolbeault.projectiveConePoint n s hs x).val,
    (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).le (ProjectiveTwist.Cone.Dolbeault.projectiveConePoint n s hs x).property⟩

theorem projectiveTwistAnalyticConeCoordinates_evaluate (n : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s))))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (projectiveTwistAnalyticConeCoordinates n s i hi j d a).val.val x =
      x.val i ^ d * ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s i hi j d a (projectiveAnalyticConePoint n s hs x) := by
  let b := (projectiveIntersectionOpenSectionIso n s j d).inv a
  have hba : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map
      (homOfLE (Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen n s).ge).op b = a :=
    (projectiveIntersectionOpenSectionIso_hom n s j d b).symm.trans
      ((projectiveIntersectionOpenSectionIso n s j d).inv_hom_id_apply a)
  change (ProjectiveTwist.Cone.Dolbeault.projectiveTwistConeCoordinates n s i hi j d b).val.val x = _
  exact (ProjectiveTwist.Cone.Dolbeault.projectiveTwistConeCoordinates_evaluate n s hs i hi j d b x).trans
    ((congrArg (x.val i ^ d * ·)
      (FrameDomainTransport.Dolbeault.projectiveTwistSectionFrame_point_transport n s i hi j d b (ProjectiveTwist.Cone.Dolbeault.projectiveConePoint n s hs x))).trans
        (congrArg (fun v : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
            (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) =>
          x.val i ^ d * ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s i hi j d v
            (projectiveAnalyticConePoint n s hs x)) hba))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.AnalyticConeCoordinates.Dolbeault
