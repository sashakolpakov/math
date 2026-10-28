import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Analytification
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Intersection Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionFrames.Dolbeault

noncomputable section

/-! Every actual analytified projective twist is a unit module on a standard
finite chart intersection, using a chosen nonvanishing coordinate as anchor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAnalytifiedTwist_intersectionUnitIso (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).over (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) ≅
      SheafOfModules.unit ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).over
        (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) := by
  rw [Projective.Intersections.Dolbeault.projectiveSchemeIntersection_eq_analyticOpen]
  exact Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi)
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionFrames.Dolbeault
