import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Cech

/-! # Acyclic Cover -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.AcyclicCover.Dolbeault

noncomputable section

/-! Every actual analytified projective twist has an acyclic standard cover.
The native Čech complex therefore computes its actual sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

abbrev projectiveTwistAdditiveSheaf (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) :=
  (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))).obj
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d)

abbrev projectiveTwistOpenRestriction (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (U : Opens (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) :=
  (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0}
    (Opens.isOpenEmbedding (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) U)).obj
      (projectiveTwistAdditiveSheaf n j d)

def projectiveTwistRestrictionIso (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    projectiveTwistOpenRestriction n j d (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) ≅
        DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
          (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) :=
  Open.UnitFrame.Dolbeault.holomorphicOpenUnitTrivializationSheafIso (RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
    (M := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d)
    (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) (IntersectionFrames.Dolbeault.projectiveAnalytifiedTwist_intersectionUnitIso n s i hi j d)

theorem projectiveTwist_intersection_cohomology_vanish (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) (q : ℕ) :
    Subsingleton (Sheaf.H.{0} (projectiveTwistOpenRestriction n j d (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))
        (q + 1)) := by
  let H := Sheaf.functorH.{0} (Opens.grothendieckTopology (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) (q + 1)
  have : Subsingleton (H.obj (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))) :=
    Projective.IntersectionAcyclicity.Dolbeault.projectiveIntersection_holomorphicFunctionSheaf_cohomology_vanish n s i hi q
  let e := H.mapIso (projectiveTwistRestrictionIso n s i hi j d)
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

theorem projectiveTwistCechIntersectionsAcyclic (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (Projective.Intersections.Dolbeault.projectiveStandardCover n) (projectiveTwistAdditiveSheaf n j d) := by
  intro p t q
  change Subsingleton (Sheaf.H.{0} (projectiveTwistOpenRestriction n j d
    (∏ᶜ fun k : Fin (p + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (t k))) (q + 1))
  rw [Projective.Intersections.Dolbeault.projectiveStandardCover_tuple_intersection]
  exact projectiveTwist_intersection_cohomology_vanish n (Finset.univ.image t) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d q

def projectiveTwistCechComparison (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (projectiveTwistAdditiveSheaf n j d).obj).homology
        (q + 1) ≅
      (Sheaf.functorH.{0} (Opens.grothendieckTopology (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (q + 1)).obj
        (projectiveTwistAdditiveSheaf n j d) :=
  SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections
    (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Projective.Intersections.Dolbeault.projectiveStandardCover n)
    (projectiveTwistAdditiveSheaf n j d) (Projective.Intersections.Dolbeault.projectiveStandardCover_covers n)
      (projectiveTwistCechIntersectionsAcyclic n j d) q

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.AcyclicCover.Dolbeault
