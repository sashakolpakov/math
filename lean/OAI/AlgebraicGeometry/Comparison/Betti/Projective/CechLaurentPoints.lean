import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CoordinateEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.MonomialEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Cech Laurent Points -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentPoints.Dolbeault

noncomputable section

/-! Actual analytic points of original projective intersections lie in the required Laurent domains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] Algebraic.Sheaves.sectionAlgebra

abbrev projectiveCechAnalyticPoints (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) :=
  Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a)

theorem projectiveCechPoint_inPatch (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (p : projectiveCechAnalyticPoints n q a) (k : Fin (q + 1)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (a k).down ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
  have hp := Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a k) p.property
  change p.val ∈ Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k).down) at hp
  rw [← Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen] at hp
  exact (Intersections.Dolbeault.mem_projectiveStandardCover n (a k).down p.val).mp hp

def projectiveCechChartCoordinates (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (p : projectiveCechAnalyticPoints n q a) : {j : Fin (n + 1) // j ≠ (a 0).down} → ℂ :=
  fun j => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a 0).down j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)

theorem projectiveCechChartCoordinates_allowed (n q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1))) (p : projectiveCechAnalyticPoints n q a)
    (j : {j : Fin (n + 1) // j ≠ (a 0).down})
    (hj : SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down) j ≠ 0) :
    projectiveCechChartCoordinates n q a p j ≠ 0 := by
  obtain ⟨k, hk⟩ := (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent_ne_zero_iff
    (fun k => (a k).down) j).mp hj
  exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero (a 0).down j.val
    ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) (projectiveCechPoint_inPatch n q a p 0)).mp
      (hk ▸ projectiveCechPoint_inPatch n q a p k)

def projectiveCechRegularEvaluation (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (p : projectiveCechAnalyticPoints n q a) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a) →+* ℂ :=
  (ContMDiffMap.evalRingHom p).comp
    (Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a)).toRingHom

def projectiveCechLaurentEvaluation (n q : ℕ) (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (p : projectiveCechAnalyticPoints n q a) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a) →+* ℂ :=
  (Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))
    (projectiveCechChartCoordinates n q a p) (projectiveCechChartCoordinates_allowed n q a p)).toRingHom.comp
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) a).toRingHom

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentPoints.Dolbeault
