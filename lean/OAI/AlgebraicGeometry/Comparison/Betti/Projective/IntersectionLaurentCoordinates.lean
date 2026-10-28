import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRegularLaurentEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap

/-! # Intersection Laurent Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionLaurentCoordinates.Dolbeault

noncomputable section

/-! Original Laurent coordinates transported to the actual finite projective intersection used by analytification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace Algebraic.Sheaves.sectionAlgebra

theorem projectiveCechAlgebraicOpen_eq (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1)) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) (fun k => ULift.up (t k)) =
      Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t) :=
  ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicCechIntersection_eq n q t

def projectiveIntersectionLaurentCoordinates (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1)) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)) ≃+*
      AddMonoidAlgebra ℂ (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t)) :=
  ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.mapIso
    (eqToIso (projectiveCechAlgebraicOpen_eq n q t)).op).commRingCatIsoToRingEquiv.trans
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k)))

def projectiveIntersectionPointToCech (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) :
    CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q (fun k => ULift.up (t k)) :=
  ⟨p.val, Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (projectiveCechAlgebraicOpen_eq n q t).ge p.property⟩

theorem projectiveIntersectionLaurentCoordinates_restrict (n q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1))
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) :
    projectiveIntersectionLaurentCoordinates n q t s =
      SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k))
        ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (projectiveCechAlgebraicOpen_eq n q t).le).op s) := by
  change SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k))
    (((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.mapIso (eqToIso (projectiveCechAlgebraicOpen_eq n q t)).op).hom s) = _
  apply congrArg (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k)))
  exact ConcreteCategory.congr_hom
    (congrArg (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (Subsingleton.elim _ _)) s

theorem projectiveIntersectionRegularSection_laurentEvaluation (n q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)) s p =
      Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t)
        (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q (fun k => ULift.up (t k)) (projectiveIntersectionPointToCech n q t p))
        (CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates_allowed n q (fun k => ULift.up (t k))
          (projectiveIntersectionPointToCech n q t p))
        (projectiveIntersectionLaurentCoordinates n q t s) := by
  rw [projectiveIntersectionLaurentCoordinates_restrict]
  have hr := Open.AffineIsoEvaluation.sectionEvaluationOn_restrict (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (projectiveCechAlgebraicOpen_eq n q t).le s (projectiveIntersectionPointToCech n q t p)
  exact hr.symm.trans (CechRegularLaurentEvaluation.Dolbeault.projectiveCechRegularSection_laurentEvaluation n q (fun k => ULift.up (t k))
    (projectiveIntersectionPointToCech n q t p) _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionLaurentCoordinates.Dolbeault
