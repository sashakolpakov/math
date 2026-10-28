import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSectionTransport

/-! # Reference Cech Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap.Dolbeault

noncomputable section

/-! The original algebraic projective twist Čech complex maps to its native analytic complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAnalyticCoverEq (n : ℕ) :
    (fun i => Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) =
      Projective.Intersections.Dolbeault.projectiveStandardCover n :=
  funext (fun i => (Projective.Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen n i).symm)

def projectiveTwistNativeCoverIso (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj ≅
      (cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj :=
  AdditiveCechCoverCongr.additiveCechCoverCongrIso (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (projectiveAnalyticCoverEq n)

abbrev projectiveAlgebraicTwistCechComplex (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :=
  (cechComplexFunctor (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf

def projectiveTwistOriginalCechMap (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveAlgebraicTwistCechComplex n j d ⟶
      (cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj :=
  Module.AnalytificationCechMap.moduleAnalytificationCechMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) ≫
      (projectiveTwistNativeCoverIso n j d).hom

theorem projectiveAlgebraicCechIntersection_eq (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1)) :
    (∏ᶜ fun k : Fin (q + 1) => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)) =
      Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t) := by
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  ext p
  change (p ∈ ((⨅ k : Fin (q + 1), Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)) ↔
    p ∈ Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)
  rw [Projective.Intersections.Dolbeault.mem_projectiveAlgebraicIntersection]
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  change (∀ k : Fin (q + 1), p ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)) ↔
    ∀ i ∈ Finset.univ.image t, p ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  constructor
  · intro h i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact h k
  · intro h k
    exact h (t k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

def projectiveAlgebraicCechSectionIso (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
      (op (∏ᶜ fun k : Fin (q + 1) => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k))) ≅
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
      (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) :=
  (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.mapIso
    (eqToIso (congrArg op (projectiveAlgebraicCechIntersection_eq n q t)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap.Dolbeault
