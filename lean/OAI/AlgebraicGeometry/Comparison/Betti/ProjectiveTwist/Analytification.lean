import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionHolomorphy
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Analytification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Analytification.Dolbeault

noncomputable section

/-! The actual algebraic projective twists acquire holomorphic unit frames
on the genuine standard analytic coordinate opens under original analytification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Analytification.OpenTrivialization

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAnalytifiedTwist (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))) :=
  (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)

def projectiveAnalytifiedTwist_coordinateUnitIso (n : ℕ) (i j : Fin (n + 1)) (d : ℤ) :
    (projectiveAnalytifiedTwist n j d).over (Projective.Intersections.Dolbeault.projectiveStandardCover n i) ≅
      SheafOfModules.unit ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).over
        (Projective.Intersections.Dolbeault.projectiveStandardCover n i)) := by
  rw [Projective.Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen]
  exact Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Analytification.Dolbeault
