import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionLaurentCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechConeEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConeRestriction

/-! # Laurent Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.LaurentEvaluation.Dolbeault

noncomputable section

/-! Laurent evaluation of the original projective twist analytification map on every Cech factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.MvPolynomial

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveCechConePoint (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) :
    Projective.CechLaurentPoints.Dolbeault.projectiveCechAnalyticPoints n q (fun k => ULift.up (t k)) :=
  Projective.IntersectionLaurentCoordinates.Dolbeault.projectiveIntersectionPointToCech n q t
    (Projective.AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n (Finset.univ.image t)
      (Finset.image_nonempty.mpr Finset.univ_nonempty) x)

theorem projectiveCechConePoint_coordinates (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) (j : {j : Fin (n + 1) // j ≠ t 0}) :
    Projective.CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q (fun k => ULift.up (t k)) (projectiveCechConePoint n q t x) j =
      x.val j.val / x.val (t 0) :=
  Projective.ConeRestriction.Dolbeault.projectiveAnalyticConePoint_ratio n (Finset.univ.image t)
    (Finset.image_nonempty.mpr Finset.univ_nonempty) x (t 0) j.val

def projectiveAlgebraicTwistCechLaurentCoordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1)) :
    AddMonoidAlgebra ℂ (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t)) :=
  Projective.IntersectionLaurentCoordinates.Dolbeault.projectiveIntersectionLaurentCoordinates n q t (CechConeEvaluation.Dolbeault.projectiveAlgebraicTwistCechFrameCoefficient n j d q z t)

theorem projectiveTwistCechConeValue_original_map_laurent (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) :
    CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d q ((ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q z) t x =
      x.val (t 0) ^ d * Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t)
        (Projective.CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q (fun k => ULift.up (t k)) (projectiveCechConePoint n q t x))
        (Projective.CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates_allowed n q (fun k => ULift.up (t k))
          (projectiveCechConePoint n q t x))
        (projectiveAlgebraicTwistCechLaurentCoordinates n j d q z t) :=
  (CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue_original_map n j d q z t x).trans
    (congrArg (x.val (t 0) ^ d * ·) (Projective.IntersectionLaurentCoordinates.Dolbeault.projectiveIntersectionRegularSection_laurentEvaluation n q t
      (Projective.AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n (Finset.univ.image t)
        (Finset.image_nonempty.mpr Finset.univ_nonempty) x)
      (CechConeEvaluation.Dolbeault.projectiveAlgebraicTwistCechFrameCoefficient n j d q z t)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.LaurentEvaluation.Dolbeault
