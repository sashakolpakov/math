import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopCohomology

/-! # Top Homology Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopHomologyCycles.Dolbeault

noncomputable section

/-! The analytic top cohomology coordinates evaluate the residue of each actual cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveTwistTopCechHomologyIso_homologyπ (q : ℕ) (j : Fin (q + 2)) (d : ℤ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
      (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).cycles (q + 1)) :
    (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j d).hom
      (((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
        (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).homologyπ (q + 1) z) =
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j d
      (((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
        (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj).iCycles (q + 1) z) := by
  let K := (cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover (q + 1))).obj
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf (q + 1) j d).obj
  let S := ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopShortComplex q j d
  let Z := K.cyclesIsoSc' q (q + 1) (q + 2) (by simp) (by simp)
  let E := AdditiveHomology.Cech.additiveHomologyCoefficientIso S (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue q j d)
    (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue_surjective q j d) (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue_kernel q j d)
  have h₁ := ConcreteCategory.congr_hom
    (K.π_homologyIsoSc'_hom q (q + 1) (q + 2) (by simp) (by simp)) z
  have h₂ := ConcreteCategory.congr_hom
    (AdditiveHomology.Cech.additiveHomologyCoefficientIso_homologyπ S (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue q j d)
      (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue_surjective q j d) (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCycleResidue_kernel q j d))
    (Z.hom z)
  have h₃ := AdditiveHomology.Cech.additiveCyclesIso_hom_value S (Z.hom z)
  have h₄ := ConcreteCategory.congr_hom
    (K.cyclesIsoSc'_hom_iCycles q (q + 1) (q + 2) (by simp) (by simp)) z
  change E.hom ((K.homologyIsoSc' q (q + 1) (q + 2) (by simp) (by simp)).hom
    (K.homologyπ (q + 1) z)) = _
  exact (congrArg E.hom h₁).trans (h₂.trans
    (congrArg (ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j d) (h₃.trans h₄)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopHomologyCycles.Dolbeault
