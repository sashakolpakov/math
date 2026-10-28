import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionMaps
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.AcyclicCover

/-! # Cech Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechCoordinates.Dolbeault

noncomputable section

/-! The terms of the original native Čech complex of an analytified twist are
identified with holomorphic functions on its actual finite intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveCechIntersection_eq_analyticOpen (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1)) :
    (∏ᶜ fun k : Fin (q + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (t k) : Opens (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) =
      Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)) := by
  rw [Projective.Intersections.Dolbeault.projectiveStandardCover_tuple_intersection, Projective.Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen]

def projectiveTwistCechSectionCoordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
        (op (∏ᶜ fun k : Fin (q + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (t k))) ≃+
      DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) :=
  (((AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.mapIso
    (eqToIso (congrArg op (projectiveCechIntersection_eq_analyticOpen n q t)))).addCommGroupIsoToAddEquiv).trans
      (IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunctionEquiv n (Finset.univ.image t) (t 0)
        (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d)

abbrev projectiveTwistCechFunctionCochains (n q : ℕ) :=
  ∀ t : Fin (q + 1) → Fin (n + 1),
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))

def projectiveTwistCechCoordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q ≃+
      projectiveTwistCechFunctionCochains n q :=
  (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
    (Projective.Intersections.Dolbeault.projectiveStandardCover n) q).trans
      (AddEquiv.piCongrRight (projectiveTwistCechSectionCoordinates n j d q))

theorem projectiveTwistCechCoordinates_apply (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (a : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (t : Fin (q + 1) → Fin (n + 1)) :
    projectiveTwistCechCoordinates n j d q a t =
      projectiveTwistCechSectionCoordinates n j d q t
        (Pi.π (fun b : Fin (q + 1) → Fin (n + 1) =>
          (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
            (op (∏ᶜ fun k : Fin (q + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (b k)))) t a) := by
  change projectiveTwistCechSectionCoordinates n j d q t
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
      (Projective.Intersections.Dolbeault.projectiveStandardCover n) q a t) = _
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechCoordinates.Dolbeault
