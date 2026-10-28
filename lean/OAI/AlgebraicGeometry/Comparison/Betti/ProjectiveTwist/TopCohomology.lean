import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopRepresentatives
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology

/-! # Top Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopCohomology.Dolbeault

noncomputable section

/-! Actual positive top projective twist cohomology is its homogeneous full-negative coefficient space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology.Cech

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

abbrev projectiveTwistTopShortComplex (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).sc' q (q + 1) (q + 2)

def projectiveTwistTopCycleResidue (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    (projectiveTwistTopShortComplex q j d).g.hom.ker →+
      ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) d) :=
  (TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j d).comp
    (projectiveTwistTopShortComplex q j d).g.hom.ker.subtype

theorem projectiveTwistTopCycleResidue_surjective (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    Function.Surjective (projectiveTwistTopCycleResidue q j d) := by
  intro v
  refine ⟨⟨TopRepresentatives.Dolbeault.projectiveTwistTopRepresentative (q + 1) j d v,
    TopRepresentatives.Dolbeault.projectiveTwistTopRepresentative_cycle (q + 1) j d v⟩, ?_⟩
  exact TopRepresentatives.Dolbeault.projectiveTwistTopRepresentative_residue (q + 1) j d v

theorem projectiveTwistTopCycleResidue_kernel (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    (projectiveTwistTopShortComplex q j d).abToCycles.range =
      (projectiveTwistTopCycleResidue q j d).ker := by
  apply AddSubgroup.ext
  intro z
  change (∃ b, (projectiveTwistTopShortComplex q j d).abToCycles b = z) ↔
    TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j d z.val = 0
  constructor
  · rintro ⟨b, hb⟩
    exact (TopResidue.Dolbeault.projectiveTwistTopCycle_boundary_iff q j d z.val z.property).mp
      ⟨b, congrArg Subtype.val hb⟩
  · intro hz
    obtain ⟨b, hb⟩ := (TopResidue.Dolbeault.projectiveTwistTopCycle_boundary_iff q j d z.val z.property).mpr hz
    exact ⟨b, Subtype.ext hb⟩

def projectiveTwistTopCechHomologyIso (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).homology (q + 1) ≅
      AddCommGrpCat.of ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) d) :=
  HomologicalComplex.homologyIsoSc' _ q (q + 1) (q + 2) (by simp) (by simp) ≪≫
    AdditiveHomology.Cech.additiveHomologyCoefficientIso (projectiveTwistTopShortComplex q j d)
      (projectiveTwistTopCycleResidue q j d) (projectiveTwistTopCycleResidue_surjective q j d)
        (projectiveTwistTopCycleResidue_kernel q j d)

def projectiveTwistTopCohomologyIso (q : ℕ) (j : Fin (q + 2)) (d : ℤ) :
    (Sheaf.functorH.{0} (Opens.grothendieckTopology (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints (q + 1)))
      (q + 1)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d) ≅
      AddCommGrpCat.of ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) d) :=
  (AcyclicCover.Dolbeault.projectiveTwistCechComparison (q + 1) j d q).symm ≪≫ projectiveTwistTopCechHomologyIso q j d

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopCohomology.Dolbeault
