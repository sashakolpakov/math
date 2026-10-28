import OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopResidueValues
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ZeroCycles

/-! # Zero Coefficient Values -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCoefficientValues.Dolbeault

noncomputable section

/-! The empty sector of the original degree-zero factor is identified by its cone values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

def projectiveTwistZeroCoefficient (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X 0 →+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d where
  toFun z := (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0 z ∅).val (fun _ => 0)
  map_zero' := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0))
      (congrFun (SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).map_zero ∅)
  map_add' z w := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0))
      (congrFun ((SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).map_add z w) ∅)

theorem projectiveTwistZeroCoefficient_eq_sector (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X 0) :
    projectiveTwistZeroCoefficient n j d z =
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap (Finset.univ.image (fun _ : Fin 1 => (0 : Fin (n + 1)))) d ∅
        (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv (Finset.univ.image (fun _ : Fin 1 => (0 : Fin (n + 1)))) d
          (TopResidueValues.Dolbeault.projectiveTwistCechConeSection n j d 0 z (fun _ => 0))) := rfl

theorem projectiveTwistZeroCoefficient_of_cone_values (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X 0)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d)
    (ha : ∀ x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image (fun _ : Fin 1 => (0 : Fin (n + 1)))),
      ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d 0 z (fun _ => 0) x =
        Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates ∅ x.val)) :
    projectiveTwistZeroCoefficient n j d z = a :=
  (projectiveTwistZeroCoefficient_eq_sector n j d z).trans
    (HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficient_of_single_values
      (Finset.univ.image (fun _ : Fin 1 => (0 : Fin (n + 1)))) ∅ (Finset.empty_subset _) d a
      (TopResidueValues.Dolbeault.projectiveTwistCechConeSection n j d 0 z (fun _ => 0)) ha)

theorem projectiveTwistZeroCycleCoefficient_eq (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ProjectiveTwist.ZeroCycles.Dolbeault.projectiveTwistZeroCycles n j d) :
    ProjectiveTwist.ZeroCycles.Dolbeault.projectiveTwistZeroCycleCoefficient n j d z = projectiveTwistZeroCoefficient n j d z.val := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCoefficientValues.Dolbeault
