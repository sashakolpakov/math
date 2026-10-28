import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechConeEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopResidue

/-! # Top Residue Values -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopResidueValues.Dolbeault

noncomputable section

/-! The actual top Cech coefficient is identified by the values of its original homogeneous cone section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

def projectiveTwistCechConeSection (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (t : Fin (q + 1) → Fin (n + 1)) : HomogeneousLaurent.Dolbeault.laurentHomogeneousSections (Finset.univ.image t) d :=
  AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n (Finset.univ.image t) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d
    ((CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom
      (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (Intersections.Dolbeault.projectiveStandardCover n) q z t))

theorem projectiveTwistCechConeSection_apply (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (t : Fin (q + 1) → Fin (n + 1)) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) :
    (projectiveTwistCechConeSection n j d q z t).val.val x = ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d q z t x := rfl

theorem projectiveTwistTopResidue_eq_sector (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X n) :
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j d z =
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap (Finset.univ.image (id : Fin (n + 1) → Fin (n + 1))) d Finset.univ
        (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv
          (Finset.univ.image (id : Fin (n + 1) → Fin (n + 1))) d
          (projectiveTwistCechConeSection n j d n z id)) := rfl

theorem projectiveTwistTopResidue_of_cone_values (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X n)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) d)
    (ha : ∀ x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image (id : Fin (n + 1) → Fin (n + 1))),
      ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d n z id x =
        Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates Finset.univ x.val)) :
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j d z = a := by
  have hs : (Finset.univ : Finset (Fin (n + 1))) ⊆ Finset.univ.image (id : Fin (n + 1) → Fin (n + 1)) := by
    intro i _
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact (projectiveTwistTopResidue_eq_sector n j d z).trans
    (HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficient_of_single_values
      (Finset.univ.image (id : Fin (n + 1) → Fin (n + 1))) Finset.univ hs d a
      (projectiveTwistCechConeSection n j d n z id) ha)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopResidueValues.Dolbeault
